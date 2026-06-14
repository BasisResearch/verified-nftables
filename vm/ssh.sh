#!/bin/sh
# Open a root shell in the running kernel-dev VM over vsock.
#
#   ./vm/ssh.sh                 # interactive root shell
#   ./vm/ssh.sh uname -r        # run a command and exit
#
# Thin wrapper around `mkosi ssh`, which connects to the VM started by `mkosi vm`
# (./run.sh) over AF_VSOCK using the key pair mkosi manages (enabled by
# `Ssh=yes` in mkosi.conf). Requires the VM to be running (start it with
# `make vm`).
set -e
cd "$(dirname "$0")"
exec mkosi ssh "$@"
