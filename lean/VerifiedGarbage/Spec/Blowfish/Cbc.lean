import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Spec.Cbc

/-!
# Blowfish-CBC: the contracts, on every target

**Trusted** (as every file in `Spec/`). CBC (NIST SP 800-38A §6.2,
`Spec/Cbc.lean`, defined for any block cipher) with Blowfish (Schneier, FSE
1994, `Spec/Blowfish.lean`): its encryption as `CIPH_K` and its decryption as
`CIPH⁻¹_K`, on 8-byte blocks, under the 4168-byte schedule that
`vg_blowfish_expand_key` writes.

`vg_blowfish_cbc_encrypt` and `vg_blowfish_cbc_decrypt` transform `n` whole
blocks in place, from the chaining value at `iv`, which they only read. A
caller may process a message in pieces of whole blocks: the chaining value of
the next piece is the last ciphertext block of this one (`Cbc.next`), which
the caller has (after encryption, the last block at `data`; before decryption,
the last block it decrypts). Padding is the caller's.

Only the pointers and `n` are public: no part of the chaining value may affect
timing.
-/

namespace VG.Spec.Blowfish

/-- Blowfish encryption `CIPH_K` under the schedule `k`, on blocks as lists of
8 bytes (`Cbc.Cipher`). -/
def cipher (k : Schedule) : Cbc.Cipher := fun b =>
  (encryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- Blowfish decryption `CIPH⁻¹_K` under the schedule `k`, on blocks as lists of
8 bytes. -/
def invCipher (k : Schedule) : Cbc.Cipher := fun b =>
  (decryptBlock k (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- The `n` 8-byte blocks at `p`, as lists of bytes. -/
def cbcBlocksAt (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (blocksAt m p n).map Vector.toList

/-- `vg_blowfish_cbc_encrypt(schedule: *const [u8; 4168], iv: *const [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_blowfish_cbc_decrypt` with the same signature. -/
def cbcSig : Sig where
  params := [("schedule", .array false .u8 4168), ("iv", .array false .u8 8),
    ("data", .slice true (.array .u8 8) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CBC encryption (§6.2) by Blowfish, from the chaining value at
`iv`. -/
def cbcEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A
    (post := fun schedule iv data n m m' _ =>
      cbcBlocksAt m' data n.toNat =
        Cbc.encrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CBC decryption (§6.2) by Blowfish, from the chaining value at
`iv`. -/
def cbcDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A
    (post := fun schedule iv data n m m' _ =>
      cbcBlocksAt m' data n.toNat =
        Cbc.decrypt (invCipher (scheduleAt m schedule)) (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

/-- `vg_blowfish_cbc_encrypt` on every target. -/
def cbcEncryptApi : Api where
  module := "blowfish_cbc"
  name := "vg_blowfish_cbc_encrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptContract A stack
  summary := "Blowfish-CBC encryption (NIST SP 800-38A §6.2, Schneier, FSE 1994) of whole blocks, in \
    place: replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, \
    where `C₀` is the block at `*iv`, which is only read: a further call continues the \
    message from `Cₙ`, the last block at `data` on return. `CIPH_K` is Blowfish encryption \
    under the schedule written by `vg_blowfish_expand_key`. No padding is added.\n\n\
    Contract: `VG.Spec.Blowfish.cbcEncryptContract`. Constant time: only the pointers and \
    `n` may affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_blowfish_cbc_decrypt` on every target. -/
def cbcDecryptApi : Api where
  module := "blowfish_cbc"
  name := "vg_blowfish_cbc_decrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptContract A stack
  summary := "Blowfish-CBC decryption (NIST SP 800-38A §6.2, Schneier, FSE 1994) of whole blocks, in \
    place: replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with \
    `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, where `C₀` is the block at `*iv`, which is only read: a \
    further call continues the message from `Cₙ`, the last block at `data` on entry. \
    `CIPH⁻¹_K` is Blowfish decryption under the schedule written by \
    `vg_blowfish_expand_key`. No padding is removed.\n\n\
    Contract: `VG.Spec.Blowfish.cbcDecryptContract`. Constant time: only the pointers and \
    `n` may affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Blowfish
