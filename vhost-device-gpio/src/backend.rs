// VIRTIO GPIO Emulation via vhost-user
//
// Copyright 2022 Linaro Ltd. All Rights Reserved.
//          Viresh Kumar <viresh.kumar@linaro.org>
//
// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

use log::{error, trace};
use std::num::ParseIntError;
use std::process::exit;
use std::sync::{Arc, RwLock};
use std::thread::{spawn, JoinHandle};

use clap::Parser;
use env_logger::Env;
use thiserror::Error as ThisError;
use vhost_user_backend::VhostUserDaemon;
use vm_memory::{GuestMemoryAtomic, GuestMemoryMmap};

use crate::gpio::{GpioController, GpioDevice, PhysDevice};
use crate::vhu_gpio::VhostUserGpioBackend;

#[cfg(any(test, feature = "mock_gpio"))]
use crate::mock_gpio::MockGpioDevice;
use crate::external_gpio::ExternalGpioDevice;

pub(crate) type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, ThisError)]
/// Errors related to low level GPIO helpers
pub(crate) enum Error {
    #[error("Invalid socket count: {0}")]
    SocketCountInvalid(usize),
    #[error("Socket count ({0}) doesn't match device count {1}")]
    DeviceCountMismatch(usize, usize),
    #[error("Duplicate device detected: {0}")]
    DeviceDuplicate(u32),
    #[error("Duplicate external device detected")]
    DeviceDuplicateExternal,
    #[error("Failed while parsing to integer: {0:?}")]
    ParseFailure(ParseIntError),
    #[error("Could not open gpio device: {0}")]
    CouldNotOpenDevice(crate::gpio::Error),
    #[error("Could not create gpio controller: {0}")]
    CouldNotCreateGpioController(crate::gpio::Error),
    #[error("Could not create gpio backend: {0}")]
    CouldNotCreateBackend(crate::vhu_gpio::Error),
    #[error("Could not create daemon: {0}")]
    CouldNotCreateDaemon(vhost_user_backend::Error),
    #[error("Fatal error: {0}")]
    ServeFailed(vhost_user_backend::Error),
}

const GPIO_AFTER_HELP: &str = "Each device number here will be used to \
access the corresponding /dev/gpiochipX or simulate a GPIO device \
with N pins (when feature enabled). \
Example, \"-c 4 -l 3:s4:6:s1\"\n";

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None, after_help = GPIO_AFTER_HELP)]
struct GpioArgs {
    /// Location of vhost-user Unix domain socket. This is suffixed by 0,1,2..socket_count-1.
    #[clap(short, long)]
    socket_path: String,

    /// Location of Unix domain socket where the externally-controlled GPIO backend will listen for
    /// clients.
    #[clap(short, long)]
    external_socket_path: Option<String>,

    /// Number of guests (sockets) to connect to.
    #[clap(short = 'c', long, default_value_t = 1)]
    socket_count: usize,

    /// List of GPIO devices, one for each guest, in the format
    /// [s]<N1>[:[s]<N2>].
    #[clap(short = 'l', long)]
    device_list: String,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum GpioDeviceType {
    PhysicalDevice {
        id: u32,
    },
    #[cfg(any(test, feature = "mock_gpio"))]
    SimulatedDevice {
        num_gpios: u32,
    },
    ExternalDevice {
        num_gpios: u32,
    },
}

impl GpioDeviceType {
    fn new(cfg: &str) -> Result<Self> {
        #[cfg(any(test, feature = "mock_gpio"))]
        if let Some(num) = cfg.strip_prefix('s') {
            let num_gpios = num.parse::<u32>().map_err(Error::ParseFailure)?;
            return Ok(GpioDeviceType::SimulatedDevice { num_gpios });
        }
        if let Some(num) = cfg.strip_prefix('e') {
            let num_gpios = num.parse::<u32>().map_err(Error::ParseFailure)?;
            return Ok(GpioDeviceType::ExternalDevice { num_gpios });
        }
        let id = cfg.parse::<u32>().map_err(Error::ParseFailure)?;
        Ok(GpioDeviceType::PhysicalDevice { id })
    }
}

#[derive(Debug, PartialEq)]
pub(crate) struct DeviceConfig {
    inner: Vec<GpioDeviceType>,
}

impl DeviceConfig {
    fn new() -> Self {
        Self { inner: Vec::new() }
    }

    fn contains_device(&self, device: GpioDeviceType) -> bool {
        self.inner.contains(&device)
    }

    fn push(&mut self, device: GpioDeviceType) -> Result<()> {
        match device {
            GpioDeviceType::PhysicalDevice { id } => {
                if self.contains_device(GpioDeviceType::PhysicalDevice { id }) {
                    return Err(Error::DeviceDuplicate(id));
                }
            }
            #[cfg(any(test, feature = "mock_gpio"))]
            GpioDeviceType::SimulatedDevice { num_gpios: _ } => {}
            GpioDeviceType::ExternalDevice { num_gpios: _ } => {
                let has_external = self.inner.iter()
                    .any(|dev| matches!(dev, GpioDeviceType::ExternalDevice { .. }));
                if has_external {
                    return Err(Error::DeviceDuplicateExternal);
                }
            }
        }

        self.inner.push(device);
        Ok(())
    }
}

impl TryFrom<&str> for DeviceConfig {
    type Error = Error;

    fn try_from(list: &str) -> Result<Self> {
        let list: Vec<&str> = list.split(':').collect();
        let mut devices = DeviceConfig::new();

        for info in list.iter() {
            devices.push(GpioDeviceType::new(info)?)?;
        }
        Ok(devices)
    }
}

#[derive(PartialEq, Debug)]
struct GpioConfiguration {
    socket_path: String,
    external_socket_path: String,
    socket_count: usize,
    devices: DeviceConfig,
}

impl TryFrom<GpioArgs> for GpioConfiguration {
    type Error = Error;

    fn try_from(args: GpioArgs) -> Result<Self> {
        if args.socket_count == 0 {
            return Err(Error::SocketCountInvalid(0));
        }

        let devices = DeviceConfig::try_from(args.device_list.as_str())?;

        if devices.inner.len() != args.socket_count {
            return Err(Error::DeviceCountMismatch(
                args.socket_count,
                devices.inner.len(),
            ));
        }

        Ok(GpioConfiguration {
            socket_path: args.socket_path,
            socket_count: args.socket_count,
            external_socket_path: args.external_socket_path
                .unwrap_or_else(|| "gpio.socket".into()),
            devices,
        })
    }
}

fn start_device_backend<D: GpioDevice>(device: D, socket: String) -> Result<()> {
    let controller = GpioController::new(device).map_err(Error::CouldNotCreateGpioController)?;
    let backend = Arc::new(RwLock::new(
        VhostUserGpioBackend::new(controller).map_err(Error::CouldNotCreateBackend)?,
    ));

    let mut daemon = VhostUserDaemon::new(
        String::from("vhost-device-gpio-backend"),
        backend.clone(),
        GuestMemoryAtomic::new(GuestMemoryMmap::new()),
    )
    .map_err(Error::CouldNotCreateDaemon)?;

    daemon.serve(&socket).map_err(Error::ServeFailed)?;

    Ok(())
}

fn start_backend(args: GpioArgs) -> Result<()> {
    let config = GpioConfiguration::try_from(args)?;
    let mut handles = Vec::new();

    for i in 0..config.socket_count {
        let socket = config.socket_path.to_owned() + &i.to_string();
        let external_socket = config.external_socket_path.to_owned();
        let cfg = config.devices.inner[i];

        let handle: JoinHandle<Result<()>> = spawn(move || loop {
            // A separate thread is spawned for each socket and can
            // connect to a separate guest. These are run in an
            // infinite loop to not require the daemon to be restarted
            // once a guest exits.
            //
            // However if we fail to spawn (due to bad config or
            // other reason) we will bail out of the spawning and
            // propagate the error back to gpio_init().
            match cfg {
                GpioDeviceType::PhysicalDevice { id } => {
                    let controller = PhysDevice::open(id).map_err(Error::CouldNotOpenDevice)?;
                    start_device_backend(controller, socket.clone())?;
                }
                #[cfg(any(test, feature = "mock_gpio"))]
                GpioDeviceType::SimulatedDevice { num_gpios } => {
                    let controller = MockGpioDevice::open(num_gpios).unwrap(); // cannot fail
                    start_device_backend(controller, socket.clone())?;
                }
                GpioDeviceType::ExternalDevice { num_gpios } => {
                    trace!("starting external device with {num_gpios} lines");
                    let controller = ExternalGpioDevice::open_external(
                        num_gpios,
                        external_socket.clone(),
                    );
                    start_device_backend(controller, socket.clone())?;
                }
            };
        });

        handles.push(handle);
    }

    for handle in handles {
        handle.join().map_err(std::panic::resume_unwind).unwrap()?;
    }

    Ok(())
}

pub(crate) fn gpio_init() {
    let env = Env::default().filter_or("RUST_LOG", "info");
    env_logger::init_from_env(env);

    if let Err(e) = start_backend(GpioArgs::parse()) {
        error!("Fatal error starting backend: {e}");
        exit(1);
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use super::*;

    impl DeviceConfig {
        pub fn new_with(devices: Vec<u32>) -> Self {
            DeviceConfig {
                inner: devices
                    .into_iter()
                    .map(|id| GpioDeviceType::PhysicalDevice { id })
                    .collect(),
            }
        }
    }

    fn get_cmd_args(path: &str, devices: &str, count: usize) -> GpioArgs {
        GpioArgs {
            socket_path: path.to_string(),
            socket_count: count,
            device_list: devices.to_string(),
        }
    }

    #[test]
    fn test_gpio_device_config() {
        let mut config = DeviceConfig::new();

        config
            .push(GpioDeviceType::PhysicalDevice { id: 5 })
            .unwrap();
        config
            .push(GpioDeviceType::PhysicalDevice { id: 6 })
            .unwrap();

        assert_matches!(
            config
                .push(GpioDeviceType::PhysicalDevice { id: 5 })
                .unwrap_err(),
            Error::DeviceDuplicate(5)
        );
    }

    #[test]
    fn test_gpio_parse_failure() {
        let socket_name = "vgpio.sock";

        // Invalid device number
        let cmd_args = get_cmd_args(socket_name, "1:4d:5", 3);
        assert_matches!(
            GpioConfiguration::try_from(cmd_args).unwrap_err(),
            Error::ParseFailure(e) if e == "4d".parse::<u32>().unwrap_err()
        );

        // Zero socket count
        let cmd_args = get_cmd_args(socket_name, "1:4", 0);
        assert_matches!(
            GpioConfiguration::try_from(cmd_args).unwrap_err(),
            Error::SocketCountInvalid(0)
        );

        // Duplicate client address: 4
        let cmd_args = get_cmd_args(socket_name, "1:4:5:6:4", 5);
        assert_matches!(
            GpioConfiguration::try_from(cmd_args).unwrap_err(),
            Error::DeviceDuplicate(4)
        );

        // Device count mismatch
        let cmd_args = get_cmd_args(socket_name, "1:4:5:6", 5);
        assert_matches!(
            GpioConfiguration::try_from(cmd_args).unwrap_err(),
            Error::DeviceCountMismatch(5, 4)
        );

        // Parse mixed device and simulated
        let cmd_args = get_cmd_args(socket_name, "1:s4", 2);
        assert_matches!(GpioConfiguration::try_from(cmd_args), Ok(_));
    }

    #[test]
    fn test_gpio_parse_successful() {
        let socket_name = "vgpio.sock";

        // Match expected and actual configuration
        let cmd_args = get_cmd_args(socket_name, "1:4:32:21:5", 5);
        let config = GpioConfiguration::try_from(cmd_args).unwrap();

        let expected_devices = DeviceConfig::new_with(vec![1, 4, 32, 21, 5]);
        let expected_config = GpioConfiguration {
            socket_count: 5,
            socket_path: String::from(socket_name),
            devices: expected_devices,
        };

        assert_eq!(config, expected_config);
    }

    #[test]
    fn test_gpio_fail_listener_mock() {
        let socket_name = "~/path/not/present/gpio";
        let cmd_args = get_cmd_args(socket_name, "s1:s4:s3:s5", 4);

        assert_matches!(start_backend(cmd_args).unwrap_err(), Error::ServeFailed(_));
    }
}
