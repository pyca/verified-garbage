module

public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Spec.Zeroize
public import VerifiedGarbage.TCB.Artifact

/-!
# AES-CBC, leaving nothing in `scratch`: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_cbc_encrypt_scrubbed` and `vg_aes_cbc_decrypt_scrubbed`, for any
target: `A` is the target's calling convention. They are those of
`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` (`Spec/Cbc/Contract.lean`),
with the same signature (`aesSig`), and leave nothing they computed in
`scratch`: each of its bytes on return is unchanged or zero
(`Zeroize.scrubbed`).

These are the functions for a caller that releases `scratch` on return;
the others leave it unspecified, so that the verified code that calls them
with working space of its own pays for no wipe. The names are transitional:
the plain names are those of the functions without the guarantee until
the Rust code no longer calls them and they are no longer registered, and
then these take them.
-/

@[expose] public section

namespace VG.Spec.Cbc

/-- `aesEncryptContract`, and each byte of `scratch` unchanged or zero on
return. -/
def aesEncryptScrubbedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n scratch m m' _ =>
      (∀ key, Aes.KeySchedule m schedule rounds.toNat key →
        let ciph := aes key
        let cs := encrypt ciph (Aes.bytesAt m iv 16) (blocksAt m data n.toNat)
        blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs) ∧
      Zeroize.scrubbed m m' scratch 2176)
    (stack := stack)

/-- `aesDecryptContract`, and each byte of `scratch` unchanged or zero on
return. -/
def aesDecryptScrubbedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  aesSig.contract A
    (pre := fun _schedule rounds _iv _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds iv data n scratch m m' _ =>
      (∀ key, Aes.KeySchedule m schedule rounds.toNat key →
        let ciphInv := aesInv key
        let cs := blocksAt m data n.toNat
        blocksAt m' data n.toNat = decrypt ciphInv (Aes.bytesAt m iv 16) cs ∧
          Aes.bytesAt m' iv 16 = next (Aes.bytesAt m iv 16) cs) ∧
      Zeroize.scrubbed m m' scratch 2176)
    (stack := stack)

/-- `vg_aes_cbc_encrypt_scrubbed` on every target. -/
def aesEncryptScrubbedApi : Api where
  module := "aes_cbc"
  name := "vg_aes_cbc_encrypt_scrubbed"
  sig := aesSig
  contracts := some fun A stack => aesEncryptScrubbedContract A stack
  summary := "AES-CBC encryption (NIST SP 800-38A §6.2) of whole blocks, in place, as \
    `vg_aes_cbc_encrypt`: replaces the `n` 16-byte blocks `P₁ … Pₙ` at `data` with \
    `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` (leaving \
    it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` is AES \
    (FIPS 197) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` \
    bytes of `*schedule`, as `vg_aes_expand_key` writes it. No padding is added. Each byte \
    of `scratch` is unchanged or zero on return.\n\n\
    Contract: `VG.Spec.Cbc.aesEncryptScrubbedContract`. Constant time: only the pointers, \
    `rounds` and `n` may affect timing, not the key schedule, the chaining value or the data."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- `vg_aes_cbc_decrypt_scrubbed` on every target. -/
def aesDecryptScrubbedApi : Api where
  module := "aes_cbc"
  name := "vg_aes_cbc_decrypt_scrubbed"
  sig := aesSig
  contracts := some fun A stack => aesDecryptScrubbedContract A stack
  summary := "AES-CBC decryption (NIST SP 800-38A §6.2) of whole blocks, in place, as \
    `vg_aes_cbc_decrypt`: replaces the `n` 16-byte blocks `C₁ … Cₙ` at `data` with \
    `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the \
    last block at `data` on entry (leaving it unchanged if `n = 0`), so that a further call \
    continues the message. `CIPH⁻¹_K` is the AES inverse cipher (FIPS 197 §5.3) with \
    `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` bytes of \
    `*schedule`, as `vg_aes_expand_key` writes it. No padding is removed. Each byte of \
    `scratch` is unchanged or zero on return.\n\n\
    Contract: `VG.Spec.Cbc.aesDecryptScrubbedContract`. Constant time: only the pointers, \
    `rounds` and `n` may affect timing, not the key schedule, the chaining value or the data."
  safety := ["`rounds` must be 10, 12 or 14."]

end VG.Spec.Cbc
