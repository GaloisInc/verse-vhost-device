import select
import socket
import sys


def main():
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    sock.connect('./gpio.socket')

    recv_buf = bytearray()

    while True:
        read_fds, write_fds, error_fds = select.select((sock, sys.stdin), (), ())

        for fd in read_fds:
            if fd is sock:
                recv_buf += sock.recv(4096)
                for i in range(0, len(recv_buf), 2):
                    line = recv_buf[i]
                    value = recv_buf[i + 1]
                    if value == 255:
                        value = -1
                    print('output: %d = %d' % (line, value))
                end = len(recv_buf) - len(recv_buf) % 2
                del recv_buf[:end]
            elif fd is sys.stdin:
                s = sys.stdin.readline()
                line_str, _, value_str = s.partition('=')
                try:
                    line = int(line_str.strip())
                except ValueError:
                    print('bad line index %r' % line_str)
                    continue
                try:
                    value = int(value_str.strip())
                except ValueError:
                    print('bad value %r' % line_str)
                    continue
                if value not in (0, 1):
                    print('bad value %d' % value)
                    continue
                print('input: %d = %d' % (line, value))
                sock.send(bytes((line, value)))
            else:
                assert False, 'unexpected fd %r' % (fd,)



if __name__ == '__main__':
    main()
