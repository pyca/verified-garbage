import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Spec.Cbc.Contract

/-!
# SM4-CBC: the contracts, on every target

**Trusted** (as every file in `Spec/`). CBC (NIST SP 800-38A §6.2,
`Spec/Cbc.lean`, defined for any block cipher) with SM4 (GB/T 32907-2016,
`Spec/Sm4.lean`): its forward function (§7.1) as `CIPH_K`, and its inverse
(§7.2, the same rounds with the round keys in reverse order) as
`CIPH⁻¹_K`, under the 128-byte schedule that `vg_sm4_expand_key` writes.

`vg_sm4_cbc_encrypt` and `vg_sm4_cbc_decrypt` transform `n` whole blocks in
place, from the chaining value at `iv`, which they only read. A caller may
process a message in pieces of whole blocks: the chaining value of the next
piece is the last ciphertext block of this one (`Cbc.next`), which the
caller has (after encryption, the last block at `data`; before decryption,
the last block it decrypts). Padding is the caller's.

Only the pointers and `n` are public: no part of the chaining value may
affect timing.
-/

namespace VG.Spec.Sm4

/-- SM4's inverse function `CIPH⁻¹_K` (§7.2) under the schedule `k`, on
blocks as lists of 16 bytes (`Cbc.Cipher`). -/
def invCipher (k : Schedule) : Cbc.Cipher := fun b =>
  (decryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- `vg_sm4_cbc_encrypt(schedule: *const [u8; 128], iv: *const [u8; 16], data: *mut [u8; 16], n: usize)`,
and `vg_sm4_cbc_decrypt` with the same signature. -/
def cbcSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array false .u8 16),
    ("data", .slice true (.array .u8 16) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CBC encryption (§6.2) by SM4, from the chaining value at `iv`. -/
def cbcEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A
    (post := fun schedule iv data n m m' _ =>
      Cbc.blocksAt m' data n.toNat =
        Cbc.encrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CBC decryption (§6.2) by SM4, from the chaining value at `iv`. -/
def cbcDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A
    (post := fun schedule iv data n m m' _ =>
      Cbc.blocksAt m' data n.toNat =
        Cbc.decrypt (invCipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16) (Cbc.blocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_cbc_encrypt` on every target. -/
def cbcEncryptApi : Api where
  module := "sm4_cbc"
  name := "vg_sm4_cbc_encrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptContract A stack
  summary := "SM4-CBC encryption (NIST SP 800-38A §6.2, GB/T 32907-2016 §7.1) of whole blocks, in \
    place: replaces the `n` 16-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, \
    where `C₀` is the block at `*iv`, which is only read: a further call continues the message \
    from `Cₙ`, the last block at `data` on return. `CIPH_K` is SM4 under the schedule written by \
    `vg_sm4_expand_key`. No padding is added.\n\n\
    Contract: `VG.Spec.Sm4.cbcEncryptContract`. Constant time: only the pointers and `n` may \
    affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_sm4_cbc_decrypt` on every target. -/
def cbcDecryptApi : Api where
  module := "sm4_cbc"
  name := "vg_sm4_cbc_decrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptContract A stack
  summary := "SM4-CBC decryption (NIST SP 800-38A §6.2, GB/T 32907-2016 §7.2) of whole blocks, in \
    place: replaces the `n` 16-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, \
    where `C₀` is the block at `*iv`, which is only read: a further call continues the message \
    from `Cₙ`, the last block at `data` on entry. `CIPH⁻¹_K` is SM4's decryption under the schedule written by `vg_sm4_expand_key`. No \
    padding is removed.\n\n\
    Contract: `VG.Spec.Sm4.cbcDecryptContract`. Constant time: only the pointers and `n` may \
    affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Sm4
