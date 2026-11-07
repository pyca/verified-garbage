module

public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Spec.Zeroize
public import VerifiedGarbage.TCB.Artifact

/-!
# AES-ECB: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, for any target: `A` is the
target's calling convention. They are those of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` (`Spec/Aes/Contract.lean`), with the same signature
(`Aes.blocksSig`), and leave nothing they computed in `scratch`: each of its
bytes on return is unchanged or zero (`Zeroize.scrubbed`). ECB (NIST
SP 800-38A §6.1) is the block cipher applied to each block.

The blocks functions themselves leave `scratch` unspecified, so that the
verified code that calls them with working space of its own pays for no
wipe; these are the functions for a caller that releases `scratch` on
return.
-/

@[expose] public section

namespace VG.Spec.AesEcb

open VG.Spec.Aes

/-- For `rounds` of 10, 12 or 14, and every key `key` whose key schedule is
at `schedule` with `rounds` rounds (`KeySchedule`): replaces each of the `n`
blocks at `data` with `CIPHER(·, Nr, KEYEXPANSION(key))`, and leaves each
byte of `scratch` unchanged or zero. The key schedule and the data are
secret. -/
def encryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (pre := fun _schedule rounds _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds data n scratch m m' _ =>
      (∀ key, KeySchedule m schedule rounds.toNat key →
        statesAt m' data n.toNat =
          (statesAt m data n.toNat).map (cipher (Aes.rounds (key.length / 4)) (expandKey key))) ∧
      Zeroize.scrubbed m m' scratch 2048)
    (stack := stack)

/-- For `rounds` of 10, 12 or 14, and every key `key` whose key schedule is
at `schedule` with `rounds` rounds (`KeySchedule`): replaces each of the `n`
blocks at `data` with `INVCIPHER(·, Nr, KEYEXPANSION(key))`, and leaves each
byte of `scratch` unchanged or zero. The key schedule and the data are
secret. -/
def decryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blocksSig.contract A
    (pre := fun _schedule rounds _data _n _scratch _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun schedule rounds data n scratch m m' _ =>
      (∀ key, KeySchedule m schedule rounds.toNat key →
        statesAt m' data n.toNat =
          (statesAt m data n.toNat).map (invCipher (Aes.rounds (key.length / 4)) (expandKey key))) ∧
      Zeroize.scrubbed m m' scratch 2048)
    (stack := stack)

/-- `vg_aes_ecb_encrypt` on every target. -/
def encryptApi : Api where
  module := "aes_ecb"
  name := "vg_aes_ecb_encrypt"
  sig := blocksSig
  contracts := some fun A stack => encryptContract A stack
  summary := "AES-ECB encryption (NIST SP 800-38A §6.1) of whole blocks, in place: replaces \
    each of the `n` 16-byte blocks at `data` with its encryption by AES (FIPS 197 §5.1, \
    `CIPHER`) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` bytes \
    of `*schedule`, as `vg_aes_expand_key` writes it. No padding is added. Each byte of \
    `scratch` is unchanged or zero on return.\n\n\
    Contract: `VG.Spec.AesEcb.encryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule or the data."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- `vg_aes_ecb_decrypt` on every target. -/
def decryptApi : Api where
  module := "aes_ecb"
  name := "vg_aes_ecb_decrypt"
  sig := blocksSig
  contracts := some fun A stack => decryptContract A stack
  summary := "AES-ECB decryption (NIST SP 800-38A §6.1) of whole blocks, in place: replaces \
    each of the `n` 16-byte blocks at `data` with its decryption by AES (FIPS 197 §5.3, \
    `INVCIPHER`) with `rounds` rounds and the key schedule in the first `16 * (rounds + 1)` \
    bytes of `*schedule`, as `vg_aes_expand_key` writes it (the forward cipher's schedule). \
    No padding is removed. Each byte of `scratch` is unchanged or zero on return.\n\n\
    Contract: `VG.Spec.AesEcb.decryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the key schedule or the data."
  safety := ["`rounds` must be 10, 12 or 14."]

end VG.Spec.AesEcb
