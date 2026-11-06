module

public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Cfb.Final

/-!
# IDEA-CFB64 of a message's last piece: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_idea_cfb64_encrypt_final` and `vg_idea_cfb64_decrypt_final`: the CFB64
functions of `Spec/Idea/Cfb.lean` (the same `CIPH_K`, schedule, and public
and secret arguments) with the data `len` bytes rather than `n` whole
blocks, so that they also take a partial last segment, as
`Spec/Cfb/Final.lean` defines it (`Cfb.encryptFinal`, `Cfb.decryptFinal`): a
message's last piece, of any length. Existing contracts are unchanged.

Each leaves in `iv` the last ciphertext block when `len` is a multiple of 8,
so that a further call continues the message, and `Oₙ`, keystream, after a
partial last segment, after which the message must end.
-/

@[expose] public section

namespace VG.Spec.Idea

/-- `vg_idea_cfb64_encrypt_final(schedule: *const [u8; 104], iv: *mut [u8; 8], data: *mut u8, len: usize)`,
and `vg_idea_cfb64_decrypt_final` with the same signature: `cfbSig` with the
data `len` bytes. -/
def cfbFinalSig : Sig where
  params := [("schedule", .array false .u8 104), ("iv", .array true .u8 8),
    ("data", .slice true .u8 "len")]

/-- With the schedule at `schedule`: replaces the `len` bytes at `data` with
their CFB64 encryption by IDEA, a partial last segment included, from the block
at `iv`, and that block with the one the encryption leaves (`Cfb.EncryptFinal`).
-/
def cfbEncryptFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (post := fun schedule iv data len m m' _ =>
      Cfb.EncryptFinal (cipher (scheduleAt m schedule)) 8 m m' iv data len.toNat)
    (writeArgs := true) (stack := stack)

/-- With the schedule at `schedule`: replaces the `len` bytes at `data` with
their CFB64 decryption by IDEA, a partial last segment included, from the block
at `iv`, and that block with the one the decryption leaves (`Cfb.DecryptFinal`).
-/
def cfbDecryptFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (post := fun schedule iv data len m m' _ =>
      Cfb.DecryptFinal (cipher (scheduleAt m schedule)) 8 m m' iv data len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_idea_cfb64_encrypt_final` on every target. -/
def cfbEncryptFinalApi : Api where
  module := "idea_cfb"
  name := "vg_idea_cfb64_encrypt_final"
  sig := cfbFinalSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptFinalContract A stack
  summary := "IDEA-CFB64 encryption (NIST SP 800-38A §6.3, with 64-bit segments; Lai, 1992, §3.3) \
    of the last piece of a message, of any length, in place: replaces its whole 8-byte blocks \
    `P₁ … Pₙ₋₁` at `data` with `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and a \
    partial last segment `Pₙ*` of `u` bytes with `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`, `Oₙ = CIPH_K(Cₙ₋₁)` (an \
    extension of SP 800-38A, which defines CFB only for whole segments, by the rule of §6.4 and \
    §6.5). Replaces `*iv` with the last ciphertext block, so that a further call continues the \
    message, if `len` is a multiple of 8 (leaving it unchanged if `len = 0`), and otherwise with \
    `Oₙ`: keystream, to be wiped, after which the message must end. `CIPH_K` is IDEA encryption \
    under the encryption subkeys written by `vg_idea_expand_key`.\n\n\
    Contract: `VG.Spec.Idea.cfbEncryptFinalContract`. Constant time: only the pointers and `len` \
    may affect timing, not the subkeys, the chaining value or the data."
  safety := []

/-- `vg_idea_cfb64_decrypt_final` on every target. -/
def cfbDecryptFinalApi : Api where
  module := "idea_cfb"
  name := "vg_idea_cfb64_decrypt_final"
  sig := cfbFinalSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptFinalContract A stack
  summary := "IDEA-CFB64 decryption (NIST SP 800-38A §6.3, with 64-bit segments; Lai, 1992, §3.3) \
    of the last piece of a message, of any length, in place: replaces its whole 8-byte blocks \
    `C₁ … Cₙ₋₁` at `data` with `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and a \
    partial last segment `Cₙ*` of `u` bytes with `Pₙ* = Cₙ* ⊕ MSB_u(Oₙ)`, `Oₙ = CIPH_K(Cₙ₋₁)` (an \
    extension of SP 800-38A, which defines CFB only for whole segments, by the rule of §6.4 and \
    §6.5). Replaces `*iv` with the last ciphertext block, the last whole block at `data` on entry, \
    so that a further call continues the message, if `len` is a multiple of 8 (leaving it \
    unchanged if `len = 0`), and otherwise with `Oₙ`: keystream, to be wiped, after which the \
    message must end. `CIPH_K` is IDEA encryption under the encryption subkeys written by \
    `vg_idea_expand_key`.\n\n\
    Contract: `VG.Spec.Idea.cfbDecryptFinalContract`. Constant time: only the pointers and `len` \
    may affect timing, not the subkeys, the chaining value or the data."
  safety := []

end VG.Spec.Idea
