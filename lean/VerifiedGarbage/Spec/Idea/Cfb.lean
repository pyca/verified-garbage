import VerifiedGarbage.Spec.Idea.Cbc
import VerifiedGarbage.Spec.Cfb

/-!
# IDEA-CFB64: the contracts, on every target

**Trusted** (as every file in `Spec/`). CFB with 64-bit segments, the block
size (NIST SP 800-38A §6.3, `Spec/Cfb.lean`, defined for any block cipher),
with IDEA's encryption (Lai, 1992, §3.3, `Spec/Idea.lean`; `cipher`,
`Spec/Idea/Cbc.lean`) as `CIPH_K`, in both directions, under the encryption
subkeys that `vg_idea_expand_key` writes.

`vg_idea_cfb64_encrypt` and `vg_idea_cfb64_decrypt` transform `n` whole blocks
in place, from the block in `iv`, which they replace with the one to continue
from, the last ciphertext block (`Cbc.next`): a caller may encrypt or decrypt
a message in pieces of whole blocks, keeping `iv` between calls. A partial
last segment is the caller's.

Only the pointers and `n` are public: no part of the chaining value may affect
timing.
-/

namespace VG.Spec.Idea

/-- `vg_idea_cfb64_encrypt(schedule: *const [u8; 104], iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_idea_cfb64_decrypt` with the same signature. -/
def cfbSig : Sig where
  params := [("schedule", .array false .u8 104), ("iv", .array true .u8 8),
    ("data", .slice true (.array .u8 8) "n")]

/-- With the encryption subkeys at `schedule`: replaces the `n` blocks at
`data` with their CFB64 encryption (§6.3) by IDEA, from the block at `iv`,
and that block with the last ciphertext block (unchanged if `n = 0`). -/
def cfbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cfb.encrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- With the encryption subkeys at `schedule`: replaces the `n` blocks at
`data` with their CFB64 decryption (§6.3) by IDEA, from the block at `iv`,
and that block with the last ciphertext block, the last block at `data` on
entry (unchanged if `n = 0`). -/
def cfbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat = Cfb.decrypt (cipher (scheduleAt m schedule)) (Aes.bytesAt m iv 8) cs ∧
        Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_idea_cfb64_encrypt` on every target. -/
def cfbEncryptApi : Api where
  module := "idea_cfb"
  name := "vg_idea_cfb64_encrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptContract A stack
  summary := "IDEA-CFB64 encryption (NIST SP 800-38A §6.3, with 64-bit segments; Lai 1992 §3.3) of \
    whole blocks, in place: replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with \
    `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` (leaving \
    it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` is IDEA \
    under the encryption subkeys at `schedule`, as `vg_idea_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Idea.cfbEncryptContract`. Constant time: only the pointers and `n` \
    may affect timing, not the subkeys, the chaining value or the data."
  safety := []

/-- `vg_idea_cfb64_decrypt` on every target. -/
def cfbDecryptApi : Api where
  module := "idea_cfb"
  name := "vg_idea_cfb64_decrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptContract A stack
  summary := "IDEA-CFB64 decryption (NIST SP 800-38A §6.3, with 64-bit segments; Lai 1992 §3.3) of \
    whole blocks, in place: replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with \
    `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the \
    last block at `data` on entry (leaving it unchanged if `n = 0`), so that a further call \
    continues the message. `CIPH_K` is IDEA (also for decryption) under the encryption \
    subkeys at `schedule`, as `vg_idea_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Idea.cfbDecryptContract`. Constant time: only the pointers and `n` \
    may affect timing, not the subkeys, the chaining value or the data."
  safety := []

end VG.Spec.Idea
