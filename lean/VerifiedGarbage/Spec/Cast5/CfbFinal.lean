module

public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cfb.Final

/-!
# CAST5-CFB64 of a message's last piece: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of
`vg_cast5_cfb64_encrypt_final` and `vg_cast5_cfb64_decrypt_final`: the CFB64
functions of `Spec/Cast5/Cfb.lean` (the same `CIPH_K`, schedule, and public
and secret arguments) with the data `len` bytes rather than `n` whole
blocks, so that they also take a partial last segment, as
`Spec/Cfb/Final.lean` defines it (`Cfb.encryptFinal`, `Cfb.decryptFinal`): a
message's last piece, of any length. Existing contracts are unchanged.

Each leaves in `iv` the last ciphertext block when `len` is a multiple of 8,
so that a further call continues the message, and `Oₙ`, keystream, after a
partial last segment, after which the message must end.
-/

@[expose] public section

namespace VG.Spec.Cast5

/-- `vg_cast5_cfb64_encrypt_final(schedule: *const [u8; 128], rounds: usize, iv: *mut [u8; 8], data: *mut u8, len: usize)`,
and `vg_cast5_cfb64_decrypt_final` with the same signature: `cfbSig` with the
data `len` bytes. `rounds` is public. -/
def cfbFinalSig : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("iv", .array true .u8 8), ("data", .slice true .u8 "len")]

/-- `rounds` is 12 or 16. -/
def cfbFinalPre (pb : Nat) : Curry (cfbFinalSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _len _ => rounds.toNat = 12 ∨ rounds.toNat = 16

/-- For `rounds` of 12 or 16, and every key `K` whose subkeys are at `schedule`
with `rounds` rounds (`KeySchedule`): replaces the `len` bytes at `data` with
their CFB64 encryption by CAST5, a partial last segment included, from the block
at `iv`, and that block with the one the encryption leaves (`Cfb.EncryptFinal`).
-/
def cfbEncryptFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (pre := cfbFinalPre A.ptrBits)
    (post := fun schedule rounds iv data len m m' _ =>
      ∀ key, KeySchedule m schedule rounds.toNat key →
        Cfb.EncryptFinal (cipher (expandKey key) (Cast5.rounds key.length)) 8 m m' iv data
          len.toNat)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, and every key `K` whose subkeys are at `schedule`
with `rounds` rounds (`KeySchedule`): replaces the `len` bytes at `data` with
their CFB64 decryption by CAST5, a partial last segment included, from the block
at `iv`, and that block with the one the decryption leaves (`Cfb.DecryptFinal`).
-/
def cfbDecryptFinalContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbFinalSig.contract A (pre := cfbFinalPre A.ptrBits)
    (post := fun schedule rounds iv data len m m' _ =>
      ∀ key, KeySchedule m schedule rounds.toNat key →
        Cfb.DecryptFinal (cipher (expandKey key) (Cast5.rounds key.length)) 8 m m' iv data
          len.toNat)
    (writeArgs := true) (stack := stack)

/-- `vg_cast5_cfb64_encrypt_final` on every target. -/
def cfbEncryptFinalApi : Api where
  module := "cast5_cfb"
  name := "vg_cast5_cfb64_encrypt_final"
  sig := cfbFinalSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptFinalContract A stack
  summary := "CAST5-CFB64 encryption (NIST SP 800-38A §6.3, with 64-bit segments; RFC 2144 §2) of \
    the last piece of a message, of any length, in place: replaces its whole 8-byte blocks \
    `P₁ … Pₙ₋₁` at `data` with `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and a \
    partial last segment `Pₙ*` of `u` bytes with `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`, `Oₙ = CIPH_K(Cₙ₋₁)` (an \
    extension of SP 800-38A, which defines CFB only for whole segments, by the rule of §6.4 and \
    §6.5). Replaces `*iv` with the last ciphertext block, so that a further call continues the \
    message, if `len` is a multiple of 8 (leaving it unchanged if `len = 0`), and otherwise with \
    `Oₙ`: keystream, to be wiped, after which the message must end. `CIPH_K` is CAST5 encryption \
    with `rounds` rounds under the subkeys at `schedule`, as `vg_cast5_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Cast5.cfbEncryptFinalContract`. Constant time: only the pointers, `rounds` \
    and `len` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

/-- `vg_cast5_cfb64_decrypt_final` on every target. -/
def cfbDecryptFinalApi : Api where
  module := "cast5_cfb"
  name := "vg_cast5_cfb64_decrypt_final"
  sig := cfbFinalSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptFinalContract A stack
  summary := "CAST5-CFB64 decryption (NIST SP 800-38A §6.3, with 64-bit segments; RFC 2144 §2) of \
    the last piece of a message, of any length, in place: replaces its whole 8-byte blocks \
    `C₁ … Cₙ₋₁` at `data` with `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and a \
    partial last segment `Cₙ*` of `u` bytes with `Pₙ* = Cₙ* ⊕ MSB_u(Oₙ)`, `Oₙ = CIPH_K(Cₙ₋₁)` (an \
    extension of SP 800-38A, which defines CFB only for whole segments, by the rule of §6.4 and \
    §6.5). Replaces `*iv` with the last ciphertext block, the last whole block at `data` on entry, \
    so that a further call continues the message, if `len` is a multiple of 8 (leaving it \
    unchanged if `len = 0`), and otherwise with `Oₙ`: keystream, to be wiped, after which the \
    message must end. `CIPH_K` is CAST5 encryption with `rounds` rounds under the subkeys at \
    `schedule`, as `vg_cast5_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Cast5.cfbDecryptFinalContract`. Constant time: only the pointers, `rounds` \
    and `len` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

end VG.Spec.Cast5
