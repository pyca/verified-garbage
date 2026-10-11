import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Spec.Cfb

/-!
# CAST5-CFB64: the contracts, on every target

**Trusted** (as every file in `Spec/`). CFB with 64-bit segments, the block
size (NIST SP 800-38A §6.3, `Spec/Cfb.lean`, defined for any block cipher),
with CAST5's encryption (RFC 2144 §2, `Spec/Cast5.lean`; `cipher`,
`Spec/Cast5/Cbc.lean`) as `CIPH_K`, in both directions, under the subkeys that
`vg_cast5_expand_key` writes, with `rounds` rounds.

`vg_cast5_cfb64_encrypt` and `vg_cast5_cfb64_decrypt` transform `n` whole
blocks in place, from the block in `iv`, which they replace with the one to
continue from, the last ciphertext block (`Cbc.next`): a caller may encrypt or
decrypt a message in pieces of whole blocks, keeping `iv` between calls. A
partial last segment is the caller's.

Only the pointers, `rounds` and `n` are public: no part of the chaining value
may affect timing.
-/

namespace VG.Spec.Cast5

/-- `vg_cast5_cfb64_encrypt(schedule: *const [u8; 128], rounds: usize, iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_cast5_cfb64_decrypt` with the same signature. `rounds` is public, 12
or 16 (the precondition). -/
def cfbSig : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("iv", .array true .u8 8), ("data", .slice true (.array .u8 8) "n")]

/-- `rounds` is 12 or 16. -/
def cfbPre (pb : Nat) : Curry (cfbSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their CFB64 encryption (§6.3) by CAST5, from the block
at `iv`, and that block with the last ciphertext block (unchanged if
`n = 0`). -/
def cfbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := Cfb.encrypt (cipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their CFB64 decryption (§6.3) by CAST5, from the block
at `iv`, and that block with the last ciphertext block, the last block at
`data` on entry (unchanged if `n = 0`). -/
def cfbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat = Cfb.decrypt (cipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) cs ∧
        Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_cast5_cfb64_encrypt` on every target. -/
def cfbEncryptApi : Api where
  module := "cast5_cfb"
  name := "vg_cast5_cfb64_encrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptContract A stack
  summary := "CAST5-CFB64 encryption (NIST SP 800-38A §6.3, with 64-bit segments; RFC 2144 §2) of \
    whole blocks, in place: replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with \
    `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` (leaving \
    it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` is \
    CAST-128 encryption with `rounds` rounds under the subkeys written by \
    `vg_cast5_expand_key`.\n\n\
    Contract: `VG.Spec.Cast5.cfbEncryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

/-- `vg_cast5_cfb64_decrypt` on every target. -/
def cfbDecryptApi : Api where
  module := "cast5_cfb"
  name := "vg_cast5_cfb64_decrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptContract A stack
  summary := "CAST5-CFB64 decryption (NIST SP 800-38A §6.3, with 64-bit segments; RFC 2144 §2) of \
    whole blocks, in place: replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with \
    `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the \
    last block at `data` on entry (leaving it unchanged if `n = 0`), so that a further call \
    continues the message. `CIPH_K` is CAST-128 encryption (also for decryption) with \
    `rounds` rounds under the subkeys written by `vg_cast5_expand_key`.\n\n\
    Contract: `VG.Spec.Cast5.cfbDecryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

end VG.Spec.Cast5
