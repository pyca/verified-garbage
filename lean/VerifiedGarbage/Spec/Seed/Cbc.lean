module

public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Spec.Seed

/-!
# SEED-CBC: the contracts, on every target

**Trusted** (as every file in `Spec/`). CBC (NIST SP 800-38A §6.2,
`Spec/Cbc.lean`, defined for any block cipher) with SEED (RFC 4269 §2,
`Spec/Seed.lean`): its encryption as `CIPH_K` and its decryption as
`CIPH⁻¹_K`, on 16-byte blocks, under the 128-byte schedule that
`vg_seed_expand_key` writes.

`vg_seed_cbc_encrypt_chained` and `vg_seed_cbc_decrypt_chained` transform
`n` whole blocks in place, from the chaining value at `iv`, which they
replace with the chaining value to continue from (`Cbc.next`, the last
ciphertext block), as AES-CBC's functions do (`Spec/Cbc/Contract.lean`):
a caller may process a message in pieces of whole blocks, and keeps no
block of its own between them. Padding is the caller's.

Only the pointers and `n` are public: no part of the chaining value may affect
timing.
-/

@[expose] public section

namespace VG.Spec.Seed

/-- SEED encryption `CIPH_K` under the schedule `k`, on blocks as lists of
16 bytes (`Cbc.Cipher`). -/
def cipher (k : Schedule) : Cbc.Cipher := fun b =>
  (encryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- SEED decryption `CIPH⁻¹_K` under the schedule `k`, on blocks as lists of
16 bytes. -/
def invCipher (k : Schedule) : Cbc.Cipher := fun b =>
  (decryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- `vg_seed_cbc_encrypt_chained(schedule: *const [u8; 128], iv: *mut [u8; 16], data: *mut [u8; 16], n: usize)`,
and `vg_seed_cbc_decrypt_chained` with the same signature. -/
def cbcChainedSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CBC encryption (§6.2) by SEED, from the chaining value at `iv`, and
the chaining value with the last ciphertext block (unchanged if `n = 0`), as
`Cbc.aesEncryptContract` does. -/
def cbcEncryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cbc.encrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16)
        (Cbc.blocksAt m data n.toNat)
      Cbc.blocksAt m' data n.toNat = cs ∧
        Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CBC decryption (§6.2) by SEED, from the chaining value at `iv`, and
the chaining value with the last ciphertext block, the last block at `data`
on entry (unchanged if `n = 0`), as `Cbc.aesDecryptContract` does. -/
def cbcDecryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cbc.blocksAt m data n.toNat
      Cbc.blocksAt m' data n.toNat =
          Cbc.decrypt (invCipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_seed_cbc_encrypt_chained` on every target. -/
def cbcEncryptChainedApi : Api where
  module := "seed_cbc"
  name := "vg_seed_cbc_encrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptChainedContract A stack
  summary := "SEED-CBC encryption (NIST SP 800-38A §6.2, RFC 4269 §2) of whole blocks, in place: \
    replaces the `n` 16-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, where `C₀` \
    is the block at `*iv`, and `*iv` with `Cₙ` (leaving it unchanged if `n = 0`), so that a \
    further call continues the message. `CIPH_K` is SEED encryption under the schedule written by \
    `vg_seed_expand_key`. No padding is added.\n\n\
    Contract: `VG.Spec.Seed.cbcEncryptChainedContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_seed_cbc_decrypt_chained` on every target. -/
def cbcDecryptChainedApi : Api where
  module := "seed_cbc"
  name := "vg_seed_cbc_decrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptChainedContract A stack
  summary := "SEED-CBC decryption (NIST SP 800-38A §6.2, RFC 4269 §2) of whole blocks, in place: \
    replaces the `n` 16-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, where \
    `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the last block at `data` on entry (leaving it \
    unchanged if `n = 0`), so that a further call continues the message. `CIPH⁻¹_K` is SEED \
    decryption under the schedule written by `vg_seed_expand_key`. No padding is removed.\n\n\
    Contract: `VG.Spec.Seed.cbcDecryptChainedContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Seed
