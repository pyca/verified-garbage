module

public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.Print
public import VerifiedGarbage.TCB.Sig

/-!
# AES-GCM whole blocks with an external plaintext prefix

**Trusted** (as every file in `Spec/`). This is `encryptBlocksContract`
with the prefix convention of `sealSplitContract`: the first `src_n`
plaintext blocks come from `src`, and the remaining blocks are already at
`dst`. The prefix length is measured in 16-byte blocks.

A caller encrypting in place passes an empty source. A caller encrypting
entirely out of place sets `src_n = n`. This lets both callers share a
fused counter-mode and GHASH implementation. The signature keeps every
nonempty source disjoint from the writable buffers, as the other GCM
signatures do.

The cryptographic operations are the existing counter mode and GHASH of
NIST SP 800-38D §§6.4–6.5, composed as in §7.1 steps 3 and 5. Existing
contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-- `vg_aes_gcm_encrypt_blocks_split(ctx, rounds, counter, y, src, src_n,
dst, n, scratch)`. Counts are in whole blocks; `scratch` is 2112 bytes. -/
def encryptBlocksSplitSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("y", .array true .u8 16),
    ("src", .slice false (.array .u8 16) "src_n"),
    ("dst", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 264)]

/-- AES has 10, 12 or 14 rounds, and the external prefix fits the output. -/
def encryptBlocksSplitPre (pb : Nat) : Curry (encryptBlocksSplitSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _counter _y _src srcN _dst n _scratch _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ srcN.toNat ≤ n.toNat

/-- Encrypt the external prefix followed by the destination's original
suffix. Advance the counter by `n` and continue GHASH over the ciphertext. -/
def encryptBlocksSplitPost (pb : Nat) : encryptBlocksSplitSig.Post pb :=
  fun ctx rounds counter y src srcN dst n _scratch m m' _ =>
    let p := blocksAt m src srcN.toNat ++ (blocksAt m dst n.toNat).drop srcN.toNat
    let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) p
    blocksAt m' dst n.toNat = c ∧
      blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
      blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c

/-- The whole-block encryption contract with a public external-prefix
length. Key material, the counter, the hash accumulator and data are secret. -/
def encryptBlocksSplitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptBlocksSplitSig.contract A (pre := encryptBlocksSplitPre A.ptrBits)
    (post := encryptBlocksSplitPost A.ptrBits) (stack := stack)

/-- A shared whole-block helper for in-place and out-of-place callers. -/
def encryptBlocksSplitApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_split"
  sig := encryptBlocksSplitSig
  contracts := some fun A stack => encryptBlocksSplitContract A stack
  summary := "AES-GCM encryption of whole blocks (NIST SP 800-38D §7.1 steps 3 and 5) with an \
    external plaintext prefix: with the key context `*ctx` that `vg_aes_gcm_init` wrote for \
    `rounds` rounds, encrypts the `src_n` blocks at `src` followed by the original blocks \
    `dst[src_n..n]`, writes all `n` ciphertext blocks at `dst`, advances `*counter` by `n` \
    applications of `inc32`, and continues `*y` through GHASH over that ciphertext. Pass \
    `src_n = 0` for in-place encryption or `src_n = n` for encryption entirely out of place.\n\n\
    Contract: `VG.Spec.Gcm.encryptBlocksSplitContract`. Constant time: only the pointers, \
    `rounds`, `src_n` and `n` may affect timing, not the key context, counter, hash \
    accumulator or plaintext."
  safety := ["`rounds` must be 10, 12 or 14.", "`src_n` must be at most `n`.",
    "The contents of `scratch` on return are unspecified."]

end VG.Spec.Gcm
