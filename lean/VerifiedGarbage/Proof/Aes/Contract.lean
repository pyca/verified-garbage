module

public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.Artifact

/-!
# AES: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_aes_expand_key_scratch` is `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) with its working space passed in
`scratch`, for functions that call it with theirs.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.Spec VG.Spec.Aes

/-- `vg_aes_expand_key_scratch(key: *const u8, key_len: usize, schedule: *mut [u8; 240], scratch: *mut [u64; 64])`:
`vg_aes_expand_key` with its working space passed in `scratch`, for
functions that call it with theirs (AES-GCM's, AES-GCM-SIV's, AES-SIV's,
AES-OCB's and CMAC's). The first `16 (Nr + 1)` bytes of `schedule` hold the
key schedule on exit; the rest of it, and `scratch`, are working space. -/
def expandKeyScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 240),
    ("scratch", .array true .u64 64)]

/-- For a key of 16, 24 or 32 bytes at `key`, writes its key schedule
(`expandKey`, `16 (Nr + 1)` bytes for `Nr = key_len / 4 + 6` rounds) to
`schedule`. The key is secret. -/
def expandKeyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeyScratchSig.contract A
    (pre := fun _key keyLen _schedule _scratch _ =>
      keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32)
    (post := fun key keyLen schedule _scratch m m' _ =>
      bytesAt m' schedule (16 * (rounds (keyLen.toNat / 4) + 1)) =
        expandKey (bytesAt m key keyLen.toNat))
    (stack := stack)

end VG.Proof.Aes
