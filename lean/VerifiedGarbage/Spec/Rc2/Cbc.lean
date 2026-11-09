module

public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.TCB.Artifact

/-!
# RC2-CBC in place: contracts on every target

**Trusted** (as every file in `Spec/`). CBC (NIST SP 800-38A §6.2,
`Spec/Cbc.lean`) with RC2 (RFC 2268 §§3–4, `Spec/Rc2.lean`) on 8-byte
blocks. This does not assert that RC2 is a NIST-approved cipher.

`vg_rc2_cbc_encrypt_chained` and `vg_rc2_cbc_decrypt_chained` transform
`n` whole blocks in place, from the chaining value at `iv`, which they
replace with the chaining value to continue from (`Cbc.next`, the last
ciphertext block). A caller may process a message in pieces of whole
blocks. Neither function buffers partial blocks or adds or removes padding.

Both directions read the same 128-byte, little-endian RC2 key schedule
(`scheduleAt`), as written at the start of the context by
`vg_rc2_cbc_init`. That initialization chooses the effective key size;
these functions neither change it nor assume it equals the key's bit length.

The signature derives memory validity, non-overlap and permitted writes
from `Sig.contract`: the schedule, IV and data are separate buffers. Only
the pointers and `n` are public; the schedule, IV and data are secret.
`stack` describes an implementation's frames and calls.
-/

@[expose] public section

namespace VG.Spec.Rc2

/-- The `n` 8-byte blocks at `p`, as lists of bytes. -/
def cbcBlocksAt (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (blocksAt m p n).map Vector.toList

/-- `vg_rc2_cbc_encrypt_chained(schedule: *const [u8; 128], iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_rc2_cbc_decrypt_chained` with the same signature. -/
def cbcChainedSig : Sig where
  params := [("schedule", .array false .u8 128), ("iv", .array true .u8 8),
    ("data", .slice true (.array .u8 8) "n")]

/-- Replaces the `n` blocks at `data` with their RC2-CBC encryption from
`iv`, under the schedule at `schedule`, and `iv` with the last ciphertext
block (unchanged if `n = 0`). -/
def cbcEncryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := Cbc.encrypt (cipher (scheduleAt m schedule)) (bytesAt m iv 8)
        (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧
        bytesAt m' iv 8 = Cbc.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- Replaces the `n` blocks at `data` with their RC2-CBC decryption from
`iv`, under the schedule at `schedule`, and `iv` with the last input
ciphertext block (unchanged if `n = 0`). -/
def cbcDecryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (post := fun schedule iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat =
          Cbc.decrypt (invCipher (scheduleAt m schedule)) (bytesAt m iv 8) cs ∧
        bytesAt m' iv 8 = Cbc.next (bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_rc2_cbc_encrypt_chained` on every target. -/
def cbcEncryptChainedApi : Api where
  module := "rc2_cbc"
  name := "vg_rc2_cbc_encrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptChainedContract A stack
  summary := "RC2-CBC encryption (RFC 2268 §§3–4, NIST SP 800-38A §6.2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, where `C₀` \
    is the block at `*iv`, and `*iv` with `Cₙ` (leaving it unchanged if `n = 0`), so that a \
    further call continues the message. `CIPH_K` is RC2 encryption under the 128-byte \
    little-endian schedule at `schedule`, as written at the start of the context by \
    `vg_rc2_cbc_init`. No padding is added.\n\n\
    Contract: `VG.Spec.Rc2.cbcEncryptChainedContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

/-- `vg_rc2_cbc_decrypt_chained` on every target. -/
def cbcDecryptChainedApi : Api where
  module := "rc2_cbc"
  name := "vg_rc2_cbc_decrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptChainedContract A stack
  summary := "RC2-CBC decryption (RFC 2268 §§3–4, NIST SP 800-38A §6.2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, where `C₀` \
    is the block at `*iv`, and `*iv` with `Cₙ`, the last block at `data` on entry (leaving it \
    unchanged if `n = 0`), so that a further call continues the message. `CIPH⁻¹_K` is RC2 \
    decryption under the same 128-byte little-endian schedule as encryption, as written at \
    the start of the context by `vg_rc2_cbc_init`. No padding is removed.\n\n\
    Contract: `VG.Spec.Rc2.cbcDecryptChainedContract`. Constant time: only the pointers and `n` \
    may affect timing, not the schedule, the chaining value or the data."
  safety := []

end VG.Spec.Rc2
