import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Spec.Cfb

/-!
# Triple DES-CFB64: the contracts, on every target

**Trusted** (as every file in `Spec/`). CFB with 64-bit segments, the block
size (NIST SP 800-38A §6.3, `Spec/Cfb.lean`, defined for any block cipher),
with Triple DES's encryption (FIPS 46-3, `Spec/TripleDes.lean`; `cipher`,
`Spec/TripleDes/Cbc.lean`) as `CIPH_K`, in both directions, under the 384-byte
schedule that `vg_triple_des_expand_key` writes.

`vg_triple_des_cfb64_encrypt` and `vg_triple_des_cfb64_decrypt` transform `n`
whole blocks in place, from the block in `iv`, which they replace with the one
to continue from, the last ciphertext block (`Cbc.next`): a caller may encrypt
or decrypt a message in pieces of whole blocks, keeping `iv` between calls. A
partial last segment is the caller's.

Only the pointers and `n` are public: no part of the chaining value may affect
timing.
-/

namespace VG.Spec.TripleDes

/-- `vg_triple_des_cfb64_encrypt(schedule: *const [u8; 384], iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_triple_des_cfb64_decrypt` with the same signature. -/
def cfbSig : Sig where
  params := [("schedule", .array false .u8 384), ("iv", .array true .u8 8),
    ("data", .slice true (.array .u8 8) "n")]

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CFB64 encryption (§6.3) by Triple DES, from the block at `iv`, and
that block with the last ciphertext block (unchanged if `n = 0`). -/
def cfbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cfb.encrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧ bytesAt m' iv 8 = Cbc.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `n` blocks at `data` with
their CFB64 decryption (§6.3) by Triple DES, from the block at `iv`, and
that block with the last ciphertext block, the last block at `data` on entry
(unchanged if `n = 0`). -/
def cfbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat = Cfb.decrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8) cs ∧
        bytesAt m' iv 8 = Cbc.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_triple_des_cfb64_encrypt` on every target. -/
def cfbEncryptApi : Api where
  module := "triple_des_cfb"
  name := "vg_triple_des_cfb64_encrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptContract A stack
  summary := "Triple DES-CFB64 encryption (NIST SP 800-38A §6.3, with 64-bit segments; FIPS 46-3) of \
    whole blocks, in place: replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with \
    `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` (leaving \
    it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` is \
    Triple DES encryption under the schedule written by `vg_triple_des_expand_key`.\n\n\
    Contract: `VG.Spec.TripleDes.cfbEncryptContract`. Constant time: only the pointers and \
    `n` may affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_triple_des_cfb64_decrypt` on every target. -/
def cfbDecryptApi : Api where
  module := "triple_des_cfb"
  name := "vg_triple_des_cfb64_decrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptContract A stack
  summary := "Triple DES-CFB64 decryption (NIST SP 800-38A §6.3, with 64-bit segments; FIPS 46-3) of \
    whole blocks, in place: replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with \
    `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the \
    last block at `data` on entry (leaving it unchanged if `n = 0`), so that a further call \
    continues the message. `CIPH_K` is Triple DES encryption (also for decryption) under the \
    schedule written by `vg_triple_des_expand_key`.\n\n\
    Contract: `VG.Spec.TripleDes.cfbDecryptContract`. Constant time: only the pointers and \
    `n` may affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.TripleDes
