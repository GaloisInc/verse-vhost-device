#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"

check_file() {
    if ! [[ -f "$1" ]]; then
        echo "Error: $1 not found; build it first" 1>&2
        return 1
    else
        age=$(( "$(date +%s)" - "$(stat -c %Y "$1")" ))
        age_hr=$(( age / 3600 ))
        age_min=$(( age / 60 % 60 ))
        age_sec=$(( age % 60 ))
        age_str=$(printf %dh%02dm%02ds "$age_hr" "$age_min" "$age_sec")
        echo "Using $1 (built $age_str ago)" 1>&2
        echo "$1"
    fi
}


edo() {
    echo " >> $*" 1>&2
    "$@"
}

package_vhost_device() {
    local kind="$1"
    shift 1

    local bin
    bin="$(check_file "target/aarch64-unknown-linux-gnu/release/vhost-device-$kind")"

    image=$(mktemp -d)
    edo mkdir -p "$image/opt/opensut/bin"
    edo cp -v "$bin" "$image/opt/opensut/bin/"

    name="verse-vhost-device-$kind"

    cargo_version="$(cargo read-manifest --manifest-path "vhost-device-$kind/Cargo.toml" | \
        python3 -c 'import json, sys; print(json.load(sys.stdin)["version"])')"
    git_rev="$(git rev-parse HEAD | cut -c -8)"
    version="${cargo_version}-g${git_rev}"

    size=$(( ( "$(stat -c %s "$bin")" + 1023) / 1024  ))

    edo mkdir -p "$image/DEBIAN"
    edo tee "$image/DEBIAN/control" <<EOF
Package: $name
Version: $version
Architecture: arm64
Maintainer: Stuart Pernsteiner <spernsteiner@galois.com>
Depends: libc6
Installed-Size: $size
Homepage: https://github.com/GaloisInc/VERSE-OpenSUT/tree/main/src/vm_runner
Description: VERSE vhost device backend - $kind
 vhost-device provides implementations of various hardware devices using
 QEMU's vhost protocol.
EOF

    edo dpkg-deb --root-owner-group --build "$image" "${name}_${version}-1_arm64.deb"

    edo rm -rf "$image"
}

: "${RUSTUP_TOOLCHAIN=stable}"
export RUSTUP_TOOLCHAIN

package_vhost_device gpio
#package_vhost_device i2c
