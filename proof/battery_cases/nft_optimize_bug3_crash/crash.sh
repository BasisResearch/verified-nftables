#!/usr/bin/env bash
# Bug 3: `nft --optimize` aborts (SIGABRT, assert) on a masked-equality match
# whose mask is a `define`d variable — e.g. the ubiquitous "mark a packet, then
# match the mark" idiom `mark & $MARK == $MARK ...`.
#
# The abort is in the optimizer's statement-matrix builder
# (src/optimize.c:529, `assert(k >= 0)` in rule_build_stmt_matrix_stmts).
# It needs only ONE rule; no merge happens.  The rule must also contain no
# statement the collector treats as "unsupported" (a plain accept/reject/counter
# is fine; a mangle `... set ...` inserts the INVALID sentinel the assert wants,
# and the crash disappears — see the last two probes).
#
# Run: unshare --net --map-root-user --map-auto -- bash crash.sh
# Expected (nft v1.1.6 and git HEAD): CRASH on the define-mask forms, ok on the
# literal-mask control and on the form carrying a mangle statement.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

run() {  # $1 = file, $2 = label
	ulimit -c 0
	nft -c -o -f "$1" >/dev/null 2>&1
	local r=$?
	if [ "$r" -eq 134 ]; then echo "CRASH (SIGABRT) | $2"; else echo "rc=$r           | $2"; fi
}

# 1) the shipped minimal reproducer
run "$here/MINIMAL_crash.nft" "mark & \$M == 0x1  accept          (define mask -> CRASH)"

# 2) literal mask, otherwise identical -> optimizer is happy
cat > "$tmp/lit.nft" <<'EOF'
table inet t {
	chain c {
		mark & 0x1 == 0x1 accept
	}
}
EOF
run "$tmp/lit.nft" "mark & 0x1 == 0x1 accept          (literal mask -> ok)"

# 3) both operands from a define, no verdict — still crashes
cat > "$tmp/both.nft" <<'EOF'
define M = 0x0bb00000
table inet t {
	chain c {
		mark & $M == $M
	}
}
EOF
run "$tmp/both.nft" "mark & \$M == \$M                   (define mask -> CRASH)"

# 4) same trigger but with a mangle statement present -> INVALID sentinel exists
cat > "$tmp/mangle.nft" <<'EOF'
define M = 0x0bb00000
table inet t {
	chain c {
		mark & $M == $M ip dscp set cs1
	}
}
EOF
run "$tmp/mangle.nft" "mark & \$M == \$M ip dscp set cs1   (unsupported stmt -> ok)"
