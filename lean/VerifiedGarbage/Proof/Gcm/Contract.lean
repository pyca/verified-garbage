module

public import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- `vg_aes_gcm_encrypt_blocks(ctx: *const [u64; 32], rounds: usize, counter: *mut [u8; 16], y: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 264])`,
and `vg_aes_gcm_decrypt_blocks` with the same signature. `rounds` is public;
`scratch` is working space. -/
def cryptBlocksSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("y", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n"), ("scratch", .array true .u64 264)]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: replaces the
`n` blocks `P` at `data` with `C = ctr32 CIPH_K CB₁ P`, where `CB₁` is the
block at `counter` (as `vg_aes_ctr32`), leaves `inc₃₂ⁿ(CB₁)` at `counter`,
and replaces the block `Y` at `y` with `GHASH_H` continued from `Y` over
`C` (as `vg_ghash`). The key context, the counter, `Y` and the data are
secret. -/
def encryptBlocksContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksSig.contract A
    (pre := fun _ctx rounds _counter _y _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: replaces the
block `Y` at `y` with `GHASH_H` continued from `Y` over the `n` blocks `C`
at `data` (as `vg_ghash`), replaces them with `ctr32 CIPH_K CB₁ C`, where
`CB₁` is the block at `counter` (as `vg_aes_ctr32`), and leaves
`inc₃₂ⁿ(CB₁)` at `counter`. The key context, the counter, `Y` and the data
are secret. -/
def decryptBlocksContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksSig.contract A
    (pre := fun _ctx rounds _counter _y _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := blocksAt m data n.toNat
      blocksAt m' data n.toNat = ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

end VG.Proof.Gcm
