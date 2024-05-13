//! GPIO backend that allows an external process to control the GPIO device.  This backend listens
//! on a socket; processes that connect to the socket can monitor the state of the output lines and
//! modify the input lines.
//!
//!
//! # Specification
//!
//! Behavior is intended to conform to the "GPIO Device" section of the VirtIO spec:
//! https://docs.oasis-open.org/virtio/virtio/v1.2/csd01/virtio-v1.2-csd01.html
//!
//! # Interrupts
//!
//! There are several operations the driver can perform related to interrupts.
//!
//! * Set the GPIO line direction to IN, OUT, or NONE.
//! * Enable the interrupt by setting the IRQ type to a value other than NONE, or disable it by
//!   setting the IRQ type to NONE.
//! * Unmask the interrupt by calling `wait_for_interrupt`.  When an interrupt occurs or the
//!   pending wait is cancelled, the call returns and the interrupt is automatically masked again.
//!
//! The spec places a number of restrictions on how the driver uses these operations.
//!
//! ## No overlapping waits
//!
//! > To unmask the interrupt, the driver MUST queue a separate pair of buffers to the eventq
//! > virtqueue for each GPIO line.
//! >
//! > The driver MUST NOT add multiple pairs of buffers for the same GPIO line on the eventq
//! > virtqueue.
//!
//! This means it's illegal to unmask the interrupt when the interrupt is already unmasked.  In
//! other words, after making a call to `wait_for_interrupt`, it's illegal to make a second call to
//! `wait_for_interrupt` before the first one returns.
//!
//! ## Can only unmask while interrupt is enabled
//!
//! > The driver MUST enable the interrupt before unmasking it.
//! >
//! > On receiving VIRTIO_GPIO_MSG_SET_IRQ_TYPE message, with VIRTIO_GPIO_IRQ_TYPE_NONE trigger
//! > type, the device MUST return the buffers, if they were received earlier, after setting the
//! > status field to VIRTIO_GPIO_IRQ_STATUS_INVALID.
//!
//! The driver can only unmask the interrupt while it is enabled.  Furthermore, if the driver
//! disables the interrupt while it is unmasked, the interrupt is automatically masked and the
//! pending `wait_for_interrupt` returns STATUS_INVALID.  This means that at all times, if the
//! interrupt is unmasked, it is also enabled.
//!
//! ## No interrupt type change while unmasked
//!
//! > In order to change the trigger type of an already enabled interrupt, the driver MUST first
//! > disable the interrupt and then re-enable it with appropriate trigger type.
//!
//! Because disabling the interrupt implicitly masks it, the interrupt type cannot be changed while
//! the interrupt is unmasked.
//!
//! ## Direction changes
//!
//! > The driver MUST NOT send IRQ messages for a GPIO line configured for output.
//! >
//! > The driver MUST set the IRQ trigger type to VIRTIO_GPIO_IRQ_TYPE_NONE once it is done using
//! > the GPIO line configured for interrupts.
//! >
//! > The device MUST discard all state information corresponding to a GPIO line, once the driver
//! > has requested to set its direction to VIRTIO_GPIO_DIRECTION_NONE.
//!
//! The spec is ambiguous on some points.  By the strict wording of the spec, the driver is
//! permitted to enable interrupts on a line whose direction is NONE, and the driver can leave the
//! interrupt enabled when switching the direction to OUT (as the driver is not "done using the
//! GPIO line" yet).  However, we interpret the rules as follows:
//!
//! * The driver must set the direction to IN before enabling an interrupt.
//! * The driver must disable the interrupt before setting the direction to OUT or NONE.
//!
//! This means that at all times, if the interrupt is enabled, the GPIO line's direction is IN.
//!
//! ## Edge-triggered and level-triggered interrupts
//!
//! > The device MUST latch an edge interrupt if the interrupt is enabled but still masked.
//! >
//! > The device MUST NOT latch an level interrupt if the interrupt is enabled but still masked.
//! >
//! > The device MUST discard any latched interrupt for a GPIO line, once interrupt is disabled for
//! > the same.
//!
//! We implement interrupt handling in terms of a virtual "interrupt signal".
//!
//! For level-triggered interrupts, the interrupt signal is active as long as the level condition
//! (high or low) is satisfied.  For edge-triggered interrupts, the interrupt signal is active as
//! long as an interrupt is latched; an interrupt becomes latched when the edge condition
//! (high-to-low or low-to-high) is observed, and the latched interrupt is discarded when it is
//! delivered (or when the interrupt is disabled).
//!
//! When the interrupt is unmasked by a `wait_for_interrupt` call, the call returns immediately if
//! the interrupt signal is active (and a latched interrupt is discarded, if appropriate).
//! Otherwise, the `wait_for_interrupt` call blocks until the interrupt signal becomes active (or
//! until the interrupt is disabled) and only then returns.

use std::fs;
use std::io::{self, Read, Write};
use std::net::Shutdown;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::sync::mpsc::{self, Sender};
use std::thread;
use log::{info, debug, trace};
use crate::gpio::{GpioDevice, Result, Error};
use crate::virtio_gpio::*;


#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
enum Direction {
    /// The GPIO line is an input to the guest/driver.  The external process can write its value.
    In,
    /// The GPIO line is an output from the driver.  The external process can read its value.
    Out,
}

/*
enum IrqState {
    /// No `wait_for_interrupt` pending, and no interrupt latched.
    Idle,
    /// An edge-triggered interrupt event is latched.  The next `wait_for_interrupt` call will
    /// immediately return `true`.
    EdgeLatched,
    /// A level-triggered interrupt state is ongoing.  Every `wait_for_interrupt` call immediately
    /// returns `true` until this state ends.
    LevelActive,
    /// A `wait_for_interrupt` call is pending.
    Pending(Sender<bool>),
}
*/

#[derive(Default)]
struct IrqState {
    edge_latched: bool,
    level_active: bool,
    pending_channel: Option<Sender<bool>>,
}

impl IrqState {
    /// Latch an edge-triggered interrupt, or deliver it immediately if a `wait_for_interrupt` call
    /// is pending.
    pub fn set_edge_latched(&mut self) {
        if let Some(channel) = self.pending_channel.take() {
            let _ = channel.send(true);
            // Channel should only be pending when there is no edge interrupt latched.  Since the
            // event was already delivered through the channel, we don't latch a new interrupt.
            debug_assert!(!self.edge_latched);
        } else {
            self.edge_latched = true;
        }
    }

    /// Set the level-triggered interrupt state to `active`.  If `active` is true and a
    /// `wait_for_interrupt` call is pending, this causes the call to return `true`.
    pub fn set_level_active(&mut self, active: bool) {
        self.level_active = active;
        if active {
            if let Some(channel) = self.pending_channel.take() {
                let _ = channel.send(true);
            }
        }
    }

    /// Check whether the interrupt signal is active.
    pub fn active(&self) -> bool {
        self.edge_latched || self.level_active
    }

    /// Set a channel where upcoming interrupt events should be delivered.  If an interrupt event
    /// is already pending, this instead delivers the event immediately via `channel`.
    pub fn set_pending(&mut self, channel: Sender<bool>) {
        if self.active() {
            // If the interrupt signal is already active, deliver an event to the channel
            // immediately.  Upon delivering an event, we discard any latched edge interrupt.
            let _ = channel.send(true);
            self.edge_latched = false;
        } else {
            self.pending_channel = Some(channel);
        }
    }

    /// Clear all pending interrupts and reset to the initial state.  This cancels any pending
    /// `wait_for_interrupt`, causing it to return `false`.
    pub fn reset(&mut self) {
        self.edge_latched = false;
        self.level_active = false;
        if let Some(channel) = self.pending_channel.take() {
            let _ = channel.send(false);
        }
    }

    /// Check whether the current IRQ state is equal to the initial/default state.
    pub fn is_default(&self) -> bool {
        let IrqState { edge_latched, level_active, ref pending_channel } = *self;
        !edge_latched && !level_active && pending_channel.is_none()
    }

    pub fn is_masked(&self) -> bool {
        self.pending_channel.is_none()
    }
}

/// Tracks the state of a single GPIO line.
///
struct LineState {
    /// GPIO line direction.  If `None`, the driver has not yet set a direction.
    dir: Option<Direction>,
    /// The input value set by the external process.  While the line is configured as an input,
    /// `GET_VALUE` calls will return this value.
    value_in: bool,
    /// The output value set by the driver.  While the line is configured as an output, this value
    /// will be sent to the external process.
    value_out: bool,
    /// Which events will trigger interrupts, causing `wait_for_interrupt` to return `true`.  If
    /// this is set to zero (all interrupts disabled), then `wait_for_interrupt` will instead
    /// return `false`.
    irq_type_mask: u8,
    /// Current interrupt state.  This records a pending `wait_for_interrupt` and/or a latched
    /// interrupt if any currently exist.
    irq_state: IrqState,
}

impl LineState {
    pub fn new() -> LineState {
        LineState {
            dir: None,
            value_in: false,
            value_out: false,
            irq_type_mask: 0,
            irq_state: IrqState::default(),
        }
    }

    /// Set the direction to `dir`.  Returns `true` if the external process should be notified of a
    /// new output value.
    pub fn set_dir(&mut self, dir: Option<Direction>) -> Result<bool> {
        if self.irq_type_mask != 0 && dir != Some(Direction::In) {
            // Driver must disable interrupts before changing direction.
            return Err(Error::GpioOldIrqTypeValid(self.irq_type_mask as u16));
        }

        // Notify when the direction changes to or from OUT.
        let notify = dir != self.dir
            && (dir == Some(Direction::Out) || self.dir == Some(Direction::Out));
        self.dir = dir;

        if dir.is_none() {
            // "The device MUST discard all state information corresponding to a GPIO line, once
            // the driver has requested to set its direction to VIRTIO_GPIO_DIRECTION_NONE."
            //
            // Here, we either clear each part of the state or assert that it was already cleared.
            let LineState {
                dir,
                value_in: _,
                ref mut value_out,
                irq_type_mask,
                ref irq_state,
            } = *self;
            debug_assert_eq!(dir, None);
            // `value_in` is controlled by the external process, so we don't reset it.
            *value_out = false;
            debug_assert_eq!(irq_type_mask, 0);
            debug_assert!(irq_state.is_default());
        }

        Ok(notify)
    }

    /// Check whether the current 
    fn value_in_matches_level_irq(&self) -> bool {
        debug_assert!(VIRTIO_GPIO_IRQ_TYPE_LEVEL_HIGH <= u8::MAX as u16);
        debug_assert!(VIRTIO_GPIO_IRQ_TYPE_LEVEL_LOW <= u8::MAX as u16);
        if self.value_in {
            self.irq_type_mask & VIRTIO_GPIO_IRQ_TYPE_LEVEL_HIGH as u8 != 0
        } else {
            self.irq_type_mask & VIRTIO_GPIO_IRQ_TYPE_LEVEL_LOW as u8 != 0
        }
    }

    fn value_in_change_matches_edge_irq(&self, old_value_in: bool) -> bool {
        let new_value_in = self.value_in;
        if old_value_in == new_value_in {
            // Not an edge.
            return false;
        }

        debug_assert!(VIRTIO_GPIO_IRQ_TYPE_EDGE_RISING <= u8::MAX as u16);
        debug_assert!(VIRTIO_GPIO_IRQ_TYPE_EDGE_FALLING <= u8::MAX as u16);

        // The IRQ type is actually a bit mask, so our cases below for `EDGE_RISING` and
        // `EDGE_FALLING` together handle `EDGE_BOTH`.
        debug_assert_eq!(
            VIRTIO_GPIO_IRQ_TYPE_EDGE_BOTH,
            VIRTIO_GPIO_IRQ_TYPE_EDGE_FALLING | VIRTIO_GPIO_IRQ_TYPE_EDGE_RISING,
        );

        if old_value_in {
            // Transition from high to low
            self.irq_type_mask & VIRTIO_GPIO_IRQ_TYPE_EDGE_FALLING as u8 != 0
        } else {
            // Transition from low to high
            self.irq_type_mask & VIRTIO_GPIO_IRQ_TYPE_EDGE_RISING as u8 != 0
        }
    }

    pub fn set_irq_type_mask(&mut self, irq_type_mask: u8) -> Result<()> {
        if irq_type_mask == self.irq_type_mask {
            return Ok(());
        }

        if irq_type_mask == 0 {
            // Disable this interrupt.
            self.irq_type_mask = irq_type_mask;

            // If the interrupt is currently unmasked, `reset()` will cancel the pending
            // `wait_for_interrupt` call.
            self.irq_state.reset();
        } else {
            // Enable this interrupt.

            // "In order to change the trigger type of an already enabled interrupt, the driver
            // MUST first disable the interrupt and then re-enable it with appropriate trigger
            // type."  It's illegal for the driver to change `irq_type_mask` while the interrupt is
            // unmasked.
            debug_assert!(self.irq_state.is_masked());

            // The interrupt can only be enabled if the direction is IN.
            if self.dir != Some(Direction::In) {
                // TODO: Provide a clearer error here.  This is the error used in `gpio.rs` for
                // this condition, but it refers to a libgpiod "line request", which is an
                // implementation detail of `PhysDevice`.
                return Err(Error::GpioLineRequestNotConfigured);
            }

            // If the interrupt is currently disabled, `irq_state` should be in the initial/default
            // state.
            if self.irq_type_mask == 0 {
                debug_assert!(self.irq_state.is_default());
            }

            self.irq_type_mask = irq_type_mask;

            // Update `irq_state.level_active` using the current `value_in` and the new IRQ type.
            let level_active = self.value_in_matches_level_irq();
            self.irq_state.set_level_active(level_active);
        }

        Ok(())
    }

    pub fn set_value_in(&mut self, value: bool) {
        let old_value_in = self.value_in;
        self.value_in = value;

        let level_active = self.value_in_matches_level_irq();
        self.irq_state.set_level_active(level_active);

        let edge = self.value_in_change_matches_edge_irq(old_value_in);
        if edge {
            self.irq_state.set_edge_latched();
        }
    }

    /// Set `value_out` to `value`.  Returns `true` if the external process should be notified of
    /// the new value.
    pub fn set_value_out(&mut self, value: bool) -> bool {
        // The output value may be set regardless of the current direction.  Regarding setting the
        // value: "The line may already be configured for output or may get configured to output
        // later, at which point this output value must be used by the device for the line."  "The
        // driver should set the value of the GPIO line, using the VIRTIO_GPIO_MSG_SET_VALUE
        // message, before setting the direction of the line to output to avoid any undesired
        // behavior."  The spec does not forbid setting the value while the direction is IN.
        let notify = self.dir == Some(Direction::Out) && value != self.value_out;
        self.value_out = value;
        notify
    }

    pub fn get_value_out(&self) -> Option<bool> {
        if self.dir != Some(Direction::Out) {
            return None;
        }
        Some(self.value_out)
    }

    pub fn start_wait_for_interrupt(&mut self, channel: Sender<bool>) -> Result<()> {
        if self.irq_type_mask == 0 {
            return Err(Error::GpioIrqNotEnabled);
        }

        if !self.irq_state.is_masked() {
            // The driver is forbidden from starting a second wait while the first is ongoing.
            //
            // TODO: Provide a clearer error here.  Currently there's no specific error variant
            // because `PhysDevice` supports this behavior, even though it's forbidden by the spec.
            return Err(Error::GpioIrqNotEnabled);
        }

        self.irq_state.set_pending(channel);
        Ok(())
    }
}


struct State {
    lines: Vec<LineState>,
    client: Option<UnixStream>,
}

pub struct ExternalGpioDevice {
    ngpio: u16,
    state: Arc<Mutex<State>>,
}

impl GpioDevice for ExternalGpioDevice {
    fn open(ngpio: u32) -> Result<Self> {
        debug!("new ExternalGpioDevice with {} lines", ngpio);
        let state = State {
            lines: (0..ngpio).map(|_| LineState::new()).collect(),
            client: None,
        };
        let state = Arc::new(Mutex::new(state));

        let state_ = state.clone();
        thread::spawn(move || {
            run_external_server(state_).unwrap();
        });

        Ok(ExternalGpioDevice {
            ngpio: ngpio as u16,
            state,
        })
    }

    fn num_gpios(&self) -> Result<u16> {
        Ok(self.ngpio)
    }
    fn gpio_name(&self, gpio: u16) -> Result<String> {
        Ok(format!("gpio{}", gpio))
    }
    fn direction(&self, gpio: u16) -> Result<u8> {
        // TODO: avoid panic when `gpio` index is out of range (similarly in other methods)
        let dir = self.state.lock().unwrap().lines[gpio as usize].dir;
        trace!("direction({gpio}) = {dir:?}");
        Ok(match dir {
            None => VIRTIO_GPIO_DIRECTION_NONE,
            Some(Direction::In) => VIRTIO_GPIO_DIRECTION_IN,
            Some(Direction::Out) => VIRTIO_GPIO_DIRECTION_OUT,
        })
    }
    fn set_direction(&self, gpio: u16, dir: u8, value: u32) -> Result<()> {
        // It's not clear from `gpio.rs` how the `value` argument should be treated.
        // `GpioController::set_direction` passes `value` based on the value used in the last call
        // to `GpioController::set_value`.  Since `VIRTIO_GPIO_MSG_SET_DIRECTION` is supposed to
        // set only the direction, not the value, we ignore the `value` argument completely.
        let _ = value;
        trace!("set_direction({gpio}, {dir}, {value})");

        let mut state = self.state.lock().unwrap();
        let dir = match dir {
            VIRTIO_GPIO_DIRECTION_NONE => None,
            VIRTIO_GPIO_DIRECTION_IN => Some(Direction::In),
            VIRTIO_GPIO_DIRECTION_OUT => Some(Direction::Out),
            _ => return Err(Error::GpioDirectionInvalid(dir as u32)),
        };
        let notify = state.lines[gpio as usize].set_dir(dir)?;
        if notify {
            let value = state.lines[gpio as usize].get_value_out();
            notify_client(&mut state.client, gpio, value);
        }
        Ok(())
    }
    fn value(&self, gpio: u16) -> Result<u8> {
        let val = self.state.lock().unwrap().lines[gpio as usize].value_in as u8;
        trace!("value({gpio}) = {val}");
        Ok(val)
    }
    fn set_value(&self, gpio: u16, value: u32) -> Result<()> {
        trace!("set_value({gpio}, {value})");
        let mut state = self.state.lock().unwrap();
        let notify = state.lines[gpio as usize].set_value_out(value != 0);
        if notify {
            let value = state.lines[gpio as usize].get_value_out();
            notify_client(&mut state.client, gpio, value);
        }
        Ok(())
    }

    fn set_irq_type(&self, gpio: u16, value: u16) -> Result<()> {
        trace!("set_irq_type({gpio}, {value})");
        let mut state = self.state.lock().unwrap();
        state.lines[gpio as usize].set_irq_type_mask(value as u8)?;
        Ok(())
    }
    fn wait_for_interrupt(&self, gpio: u16) -> Result<bool> {
        trace!("wait_for_interrupt({gpio})");
        let (send, recv) = mpsc::channel();
        {
            let mut state = self.state.lock().unwrap();
            state.lines[gpio as usize].start_wait_for_interrupt(send)?;
        }
        let ok = recv.recv().unwrap();
        trace!("wait_for_interrupt({gpio}) = {ok}");
        Ok(ok)
    }
}

fn notify_client(
    client: &mut Option<UnixStream>,
    gpio: u16,
    value: Option<bool>,
) {
    info!("send state change notification to client: {} = {:?}", gpio, value);
    if let Some(client) = client.as_mut() {
        match send_update(client, gpio as u8, value) {
            Ok(()) => {},
            Err(e) => {
                info!("error sending output notification to client: {e}");
                // Try to shut down the connection, but don't complain if it fails.  For example,
                // maybe `send_update` returned an error because the connection is already closed.
                let _ = client.shutdown(Shutdown::Both);
            },
        }
    }
}


const NO_VALUE: u8 = -1_i8 as u8;

fn send_update(stream: &mut impl Write, line: u8, value: Option<bool>) -> io::Result<()> {
    let value = match value {
        Some(true) => 1,
        Some(false) => 0,
        None => NO_VALUE,
    };
    let buf = [line, value];
    stream.write_all(&buf)?;
    Ok(())
}

fn run_external_server(state: Arc<Mutex<State>>) -> io::Result<()> {
    let path = Path::new("gpio.socket");
    if path.exists() {
        fs::remove_file(path)?;
    }
    let listener = UnixListener::bind(path)?;
    for stream in listener.incoming() {
        let mut stream = stream?;

        {
            let mut state = state.lock().unwrap();
            state.client = Some(stream.try_clone()?);
            for (i, line) in state.lines.iter().enumerate() {
                if line.dir == Some(Direction::Out) {
                    info!("send initial state to client: {} = {}", i, line.value_out);
                    send_update(&mut stream, i as u8, Some(line.value_out))?;
                }
            }
        }

        loop {
            let mut buf = [0; 2];
            // TODO: on failure, tear down connection and accept a new one, don't panic/error
            stream.read_exact(&mut buf)?;
            let line = buf[0];
            // TODO: bounds-check line and bail out early to avoid panic
            let value = match buf[1] {
                0 => false,
                1 => true,
                _ => panic!("bad input value"),
            };

            {
                let mut state = state.lock().unwrap();
                info!("received input change from client: {} = {}", line, value);
                state.lines[line as usize].set_value_in(value);
            }
        }
    }

    Ok(())
}
