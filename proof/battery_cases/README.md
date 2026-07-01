# nft-o differential BUG-HUNTER battery

Run: `bash difftest_battery.sh` (from proof/).

For each `battery_cases/*.nft`: runs OUR verified `nftc optimize` and
`nft --optimize`, loads the original and nft's recommendation into a fresh
unprivileged netns kernel, and reports divergences.

Key finding: `MINIMAL_nft_optimize_failclosed_bug.nft` — nft --optimize turns a
valid, loadable ruleset into an unloadable one ("conflicting intervals").
Confirmed against kernel (nft v1.1.6). Our verified optimizer soundly declines
the unsafe merge.
