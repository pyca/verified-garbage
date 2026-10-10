import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Spec.Cfb

/-!
# SM4-CFB128: the contracts, on every target

**Trusted** (as every file in `Spec/`). CFB with 128-bit segments (NIST
SP 800-38A §6.3, `Spec/Cfb.lean`, defined for any block cipher) with SM4's
forward function (GB/T 32907-2016 §7.1, `Spec/Sm4.lean`) as `CIPH_K`, in
both directions, under the 128-byte schedule that `vg_sm4_expand_key`
writes.

`vg_sm4_cfb128_encrypt` and `vg_sm4_cfb128_decrypt` transform `n` whole
blocks in place, from the block in `iv`, which they replace with the one to
continue from, the last ciphertext block (`Cbc.next`): a caller may encrypt
or decrypt a message in pieces of whole blocks, keeping `iv` between calls.
A partial last segment is the caller's.

Only the pointers and `n` are public: no part of the chaining value may
affect timing.
-/

namespace VG.Spec.Sm4

/-- `vg_sm4_cfb128_encrypt(schedule: *const [u8; 128], iv: *mut [u8; 16], data: *mut [u8; 16], n: usize)`,
and `vg_sm4_cfb128_decrypt` with the same signature. -/
def cfbSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CFB128 encryption (§6.3) by SM4, from the block at `iv`, and that
block with the last ciphertext block (unchanged if `n = 0`). -/
def cfbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cfb.encrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16)
        (Cbc.blocksAt m data n.toNat)
      Cbc.blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CFB128 decryption (§6.3) by SM4, from the block at `iv`, and that
block with the last ciphertext block, the last block at `data` on entry
(unchanged if `n = 0`). -/
def cfbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cbc.blocksAt m data n.toNat
      Cbc.blocksAt m' data n.toNat = Cfb.decrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 16) cs ∧
        Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_cfb128_encrypt` on every target. -/
def cfbEncryptApi : Api where
  module := "sm4_cfb"
  name := "vg_sm4_cfb128_encrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptContract A stack
  summary := "SM4-CFB128 encryption (NIST SP 800-38A §6.3, with 128-bit segments; GB/T \
    32907-2016 §7.1) of whole blocks, in place: replaces the `n` 16-byte blocks `P₁ … Pₙ` at \
    `data` with `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with \
    `Cₙ` (leaving it unchanged if `n = 0`), so that a further call continues the message. \
    `CIPH_K` is SM4 under the schedule written by `vg_sm4_expand_key`.\n\n\
    Contract: `VG.Spec.Sm4.cfbEncryptContract`. Constant time: only the pointers and `n` may \
    affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_sm4_cfb128_decrypt` on every target. -/
def cfbDecryptApi : Api where
  module := "sm4_cfb"
  name := "vg_sm4_cfb128_decrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptContract A stack
  summary := "SM4-CFB128 decryption (NIST SP 800-38A §6.3, with 128-bit segments; GB/T \
    32907-2016 §7.1) of whole blocks, in place: replaces the `n` 16-byte blocks `C₁ … Cₙ` at \
    `data` with `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with \
    `Cₙ`, the last block at `data` on entry (leaving it unchanged if `n = 0`), so that a \
    further call continues the message. `CIPH_K` is SM4's forward function (encryption) under \
    the schedule written by `vg_sm4_expand_key`.\n\n\
    Contract: `VG.Spec.Sm4.cfbDecryptContract`. Constant time: only the pointers and `n` may \
    affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Sm4
