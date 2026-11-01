module

public import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_aes_ctr32` XORs AES counter-mode keystream (with GCM's `inc₃₂`) into
whole blocks in place, from a key schedule that `vg_aes_expand_key`
(`VG.Spec.Aes.expandKeyContract`) wrote: the block-cipher work of AES-GCM
and of the modes built on AES. With a zero block it computes
`H = CIPH_K(0¹²⁸)`, and with `S` it computes the unmasked tag
`S ⊕ CIPH_K(J₀)`. It takes a `scratch` buffer of working space, sized for
the target that needs the most.

`vg_ghash` continues `GHASH_H` over whole blocks, with a `scratch` buffer of
working space, sized for the target that needs the most.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec VG.Spec.Gcm

/-- `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`.
`rounds` is public; `scratch` is working space. -/
def ctr32Sig : Sig where
  params := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("data", .slice true (.array .u8 16) "n"),
    ("scratch", .array true .u64 256)]

/-- For `rounds` of 10, 12 or 14, with the key schedule `w` in the first
`16 (rounds + 1)` bytes at `schedule`: XORs `CIPH_K(CB₁) … CIPH_K(CBₙ)`
into the `n` blocks at `data`, where `CB₁` is the block at `counter` and
`CBᵢ₊₁ = inc₃₂(CBᵢ)`, and leaves `inc₃₂ⁿ(CB₁)` at `counter`. The key
schedule, the counter and the data are secret. -/
def ctr32Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ctr32Sig.contract A
    (pre := fun _schedule rounds _counter _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds counter data n _scratch m m' _ =>
      let ciph := aesWith rounds.toNat (Aes.bytesAt m schedule (16 * (rounds.toNat + 1)))
      blocksAt m' data n.toNat = ctr32 ciph (blockAt m counter) (blocksAt m data n.toNat) ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter))
    (stack := stack)

/-- `vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`.
`scratch` is working space. -/
def ghashSig : Sig where
  params := [("h", .array false .u8 16), ("y", .array true .u8 16),
    ("data", .slice false (.array .u8 16) "n"), ("scratch", .array true .u64 32)]

/-- With the hash subkey `H` at `h` and a block `Y` at `y`: replaces `Y`
with `GHASH_H` continued from `Y` over the `n` blocks at `data`
(`Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H`). The hash subkey, `Y` and the data are secret. -/
def ghashContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ghashSig.contract A (post := fun h y data n _scratch m m' _ =>
    blockAt m' y = ghashFrom (blockAt m h) (blockAt m y) (blocksAt m data n.toNat))
    (stack := stack)

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
