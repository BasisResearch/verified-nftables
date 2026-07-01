#!/usr/bin/env bash
# vmtest.sh — reproducible end-to-end test of the verified nftc CLI against a
# REAL Linux kernel, from a clean tree.  Driven by `make vmtest`.
#
# It (1) builds the host CLI, (2) bakes the CLI + rulesets + battery into a
# rootless mkosi image running a PACKAGED Arch kernel (no custom kernel, no
# ESP/virtiofsd — direct kernel boot; see vm-e2e/mkosi.conf), (3) boots that VM
# under qemu+KVM, (4) runs e2e-battery.sh inside it over `mkosi ssh` (vsock),
# and (5) powers the VM down.  Exit code = the battery's (0 = all checks pass).
#
# Rootless: needs only /etc/subuid+subgid ranges (for `mkosi build`) and a
# world-accessible /dev/kvm (for `mkosi vm`).  No sudo.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
PROOF="$REPO/proof"
EXTRA="$HERE/mkosi.extra"
BOOTLOG="$HERE/mkosi.output/boot.log"

say() { printf '\n\033[1m>> %s\033[0m\n' "$*"; }

# ---- 1. build the verified CLI on the host -------------------------------
say "building the verified nftc CLI (make cli)"
eval "$(opam env --switch=vst 2>/dev/null || true)"
make -C "$PROOF" cli
CLI="$PROOF/extracted/_build/default/nftc_cli.exe"
[ -x "$CLI" ] || { echo "vmtest: CLI not built at $CLI" >&2; exit 1; }

# ---- 2. bake CLI + rulesets + battery into the image tree ----------------
say "staging baked-in artifacts into mkosi.extra/"
rm -rf "$EXTRA"
mkdir -p "$EXTRA/usr/local/bin" "$EXTRA/root/e2e/rules"
install -m0755 "$CLI"                 "$EXTRA/usr/local/bin/nftc"
install -m0755 "$HERE/e2e-battery.sh" "$EXTRA/root/e2e/run.sh"
install -m0644 "$HERE"/rules/*.nft    "$EXTRA/root/e2e/rules/"
for f in router.nft ruleset.nft optiplex.nft; do
  install -m0644 "$REPO/$f" "$EXTRA/root/e2e/rules/$f"
done
echo "   baked: nftc + $(ls "$EXTRA/root/e2e/rules" | wc -l) rulesets + run.sh"

# ---- 3. build the image (rootless) ---------------------------------------
say "building the mkosi VM image (rootless, packaged kernel)"
[ -f "$HERE/mkosi.key" ] || ( cd "$HERE" && mkosi genkey )
( cd "$HERE" && mkosi -f build )

# ---- 4. boot the VM and run the battery over vsock ssh -------------------
say "booting the VM (qemu+KVM, direct kernel boot)"
mkdir -p "$HERE/mkosi.output"
: > "$BOOTLOG"
( cd "$HERE" && exec mkosi vm ) </dev/null >"$BOOTLOG" 2>&1 &
VMPID=$!

cleanup() {
  ( cd "$HERE" && mkosi ssh poweroff ) >/dev/null 2>&1 || true
  for _ in $(seq 1 20); do kill -0 "$VMPID" 2>/dev/null || break; sleep 0.5; done
  kill -0 "$VMPID" 2>/dev/null && kill "$VMPID" 2>/dev/null || true
  pkill -f 'qemu-system.*e2e-vm.raw' 2>/dev/null || true
}
trap cleanup EXIT

say "waiting for the VM to come up (vsock ssh)"
up=0
for i in $(seq 1 90); do
  if ( cd "$HERE" && mkosi ssh true ) >/dev/null 2>&1; then up=1; echo "   ssh up after ~$((i*2))s"; break; fi
  kill -0 "$VMPID" 2>/dev/null || { echo "vmtest: VM process exited during boot" >&2; tail -20 "$BOOTLOG" >&2; exit 1; }
  sleep 2
done
[ "$up" = 1 ] || { echo "vmtest: VM did not become reachable" >&2; tail -20 "$BOOTLOG" >&2; exit 1; }

say "running the e2e battery inside the VM"
rc=0
( cd "$HERE" && mkosi ssh 'bash /root/e2e/run.sh' ) || rc=$?

say "battery exit code: $rc  (0 = all checks passed)"
exit "$rc"
