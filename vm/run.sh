#!/bin/sh
# Boot the kernel-dev VM (the custom kernel, via mkosi -> qemu+KVM).
#
# Reads the [Runtime] section of mkosi.conf (VMM=qemu, RAM, CPUs, vsock, ssh,
# user network, the /root/dev bind mount, console mode) and direct-boots the UKI
# built from our compiled kernel. Assumes `mkosi build` has run (`make image`).
#
# Takes over this terminal (qemu's native console); type `poweroff` inside the
# VM to stop it (Ctrl-A X kills qemu). Open a second shell with ./ssh.sh
# (`make ssh`). Read the VM's journal from the host with:  mkosi journalctl
#
# (We deliberately don't pass --forward-journal: it needs systemd-journal-remote,
# which isn't installed by default on Debian. `mkosi journalctl` works anyway.)
set -e
cd "$(dirname "$0")"
exec mkosi vm "$@"
