import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Spec.Cfb8

/-!
# Triple DES-CFB8: the contracts, on every target

**Trusted** (as every file in `Spec/`). CFB with 8-bit segments (NIST
SP 800-38A §6.3, `Spec/Cfb8.lean`, defined for any block cipher) with
Triple DES's encryption (FIPS 46-3, `Spec/TripleDes.lean`; `cipher`,
`Spec/TripleDes/Cbc.lean`) as `CIPH_K`, in both directions, on 8-byte input
blocks, under the 384-byte schedule that `vg_triple_des_expand_key` writes.

`vg_triple_des_cfb8_encrypt` and `vg_triple_des_cfb8_decrypt` transform `len`
bytes in place, from the input block in `iv`, which they replace with the one
to continue from (`Cfb8.next`): a caller may encrypt or decrypt a message in
pieces of any length, keeping `iv` between calls.

Only the pointers and `len` are public: no part of the input block may affect
timing.
-/

namespace VG.Spec.TripleDes

/-- `vg_triple_des_cfb8_encrypt(schedule: *const [u8; 384], iv: *mut [u8; 8], data: *mut u8, len: usize)`,
and `vg_triple_des_cfb8_decrypt` with the same signature. -/
def cfb8Sig : Sig where
  params := [("schedule", .array false .u8 384), ("iv", .array true .u8 8),
    ("data", .slice true .u8 "len")]

/-- With the schedule at `schedule`: replaces the `len` bytes at `data` with
their CFB8 encryption (§6.3) by Triple DES, from the input block at `iv`,
and that block with the input block of the next byte, its last `8 - len`
bytes followed by the last `len` (up to 8) ciphertext bytes (unchanged if
`len = 0`). -/
def cfb8EncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfb8Sig.contract A
    (post := fun schedule iv data len m m' _ =>
      let cs := Cfb8.encrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) (bytesAt m data len.toNat)
      bytesAt m' data len.toNat = cs ∧ bytesAt m' iv 8 = Cfb8.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `len` bytes at `data` with
their CFB8 decryption (§6.3) by Triple DES, from the input block at `iv`,
and that block with the input block of the next byte, its last `8 - len`
bytes followed by the last `len` (up to 8) bytes at `data` on entry
(unchanged if `len = 0`). -/
def cfb8DecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfb8Sig.contract A
    (post := fun schedule iv data len m m' _ =>
      let cs := bytesAt m data len.toNat
      bytesAt m' data len.toNat = Cfb8.decrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) cs ∧
        bytesAt m' iv 8 = Cfb8.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_triple_des_cfb8_encrypt` on every target. -/
def cfb8EncryptApi : Api where
  module := "triple_des_cfb8"
  name := "vg_triple_des_cfb8_encrypt"
  sig := cfb8Sig
  writeArgs := true
  contracts := some fun A stack => cfb8EncryptContract A stack
  summary := "Triple DES-CFB8 encryption (NIST SP 800-38A §6.3, with 8-bit segments; FIPS 46-3), in \
    place: replaces the `len` bytes `P#₁ … P#ₙ` at `data` with \
    `C#ⱼ = P#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))`, where `I₁` is the block at `*iv` and `Iⱼ₊₁` is `Iⱼ` \
    without its first byte, followed by `C#ⱼ`, and `*iv` with `Iₙ₊₁` (leaving it unchanged \
    if `len = 0`), so that a further call continues the message. `CIPH_K` is Triple DES \
    encryption under the schedule written by `vg_triple_des_expand_key`.\n\n\
    Contract: `VG.Spec.TripleDes.cfb8EncryptContract`. Constant time: only the pointers and \
    `len` may affect timing, not the schedule, the input block or the data."
  safety := []

/-- `vg_triple_des_cfb8_decrypt` on every target. -/
def cfb8DecryptApi : Api where
  module := "triple_des_cfb8"
  name := "vg_triple_des_cfb8_decrypt"
  sig := cfb8Sig
  writeArgs := true
  contracts := some fun A stack => cfb8DecryptContract A stack
  summary := "Triple DES-CFB8 decryption (NIST SP 800-38A §6.3, with 8-bit segments; FIPS 46-3), in \
    place: replaces the `len` bytes `C#₁ … C#ₙ` at `data` with \
    `P#ⱼ = C#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))`, where `I₁` is the block at `*iv` and `Iⱼ₊₁` is `Iⱼ` \
    without its first byte, followed by `C#ⱼ`, and `*iv` with `Iₙ₊₁` (leaving it unchanged \
    if `len = 0`), so that a further call continues the message. `CIPH_K` is Triple DES \
    encryption under the schedule written by `vg_triple_des_expand_key`.\n\n\
    Contract: `VG.Spec.TripleDes.cfb8DecryptContract`. Constant time: only the pointers and \
    `len` may affect timing, not the schedule, the input block or the data."
  safety := []

end VG.Spec.TripleDes
