# Upstream nftables bug: `ct id` byte order (draft for netfilter)

**Status:** draft — we are kernel-faithful here; nftables is not.  This is the
one adjudicated divergence (class O of `reports/corpus-divergence-bugs.md`)
where OUR compiled bytecode matches the kernel and stock `nft` does not.

## Summary

`nft` declares the `ct id` datatype **big-endian** and emits a big-endian
immediate for `ct id <n>`, but the kernel writes the conntrack id into the
comparison register as a **native-order `u32`** (no byte swap).  On a
little-endian host the two never agree, so `ct id <n>` can essentially never
match.

## Evidence (versions pinned)

- nftables `6808640` (also present on v1.1.6 and master):
  `src/ct.c:317`
  ```c
  [NFT_CT_ID] = CT_TEMPLATE("id", &integer_type, BYTEORDER_BIG_ENDIAN, 32),
  ```
  So `expr_evaluate`/`netlink_gen_data` lay the `ct id` constant in **network
  order**; a `ct id 12345` immediate is the bytes `00 00 30 39`.

- Linux `6.18.33`, `net/netfilter/nft_ct.c:173-174` (`nft_ct_get_eval`):
  ```c
  case NFT_CT_ID:
      *dest = nf_ct_get_id(ct);
  ```
  `nf_ct_get_id()` (`net/netfilter/nf_conntrack_core.c:484`) returns a plain
  `u32` (a siphash result), assigned straight into `dest->data[0]` with **no**
  `htonl`/byte-swap.  The register therefore holds the id in **host order**.

- Contrast: adjacent host-order ct keys are declared `BYTEORDER_HOST_ENDIAN` in
  the same table (e.g. `ct mark`/`ct expiration` at `src/ct.c` around line 308),
  so the `BYTEORDER_BIG_ENDIAN` on `NFT_CT_ID` is the outlier.

## Consequence

On x86-64 / arm64-LE, `nft` compares `00 00 30 39` (its big-endian immediate)
against `39 30 00 00` (the kernel's native register) — a guaranteed mismatch for
any non-palindromic id.  `ct id` matching is effectively dead on little-endian
hosts.

## What this pipeline does

We type `ct id` as a **host-endian** 4-byte integer (`Surface/Selector.v`
`["ct";"id"] -> DThostint 4`), so `Nftval.encode` lays the immediate
little-endian and it matches the kernel's native register.  Our compiled
bytecode is the kernel-correct form; the corpus/`nft` big-endian rendering is
the bug.

## Proposed fix (upstream)

Change `NFT_CT_ID`'s template byteorder from `BYTEORDER_BIG_ENDIAN` to
`BYTEORDER_HOST_ENDIAN` in `src/ct.c` (mirroring `NFT_CT_MARK`/expiration), so
the emitted immediate matches the kernel register.

## Caveat

No packet demonstration: `nf_ct_get_id` is a random siphash of the conntrack
tuple, so constructing a flow with a *known* id to count matches was out of
scope.  The adjudication is source-level against both the nft template table and
the kernel eval path, cross-checked with the corpus `ct id` payload rendering.
