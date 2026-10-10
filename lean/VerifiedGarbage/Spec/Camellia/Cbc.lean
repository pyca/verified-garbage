import VerifiedGarbage.Spec.Camellia.Ctr
import VerifiedGarbage.Spec.Cbc.Contract

/-!
# Camellia-CBC: the contracts, on every target

**Trusted** (as every file in `Spec/`). CBC (NIST SP 800-38A §6.2,
`Spec/Cbc.lean`, defined for any block cipher) with Camellia (RFC 3713
§2.3, `Spec/Camellia.lean`): its encryption as `CIPH_K` and its decryption
as `CIPH⁻¹_K`, under the subkeys of `rounds` rounds that
`vg_camellia_expand_key` writes.

`vg_camellia_cbc_encrypt` and `vg_camellia_cbc_decrypt` transform `n` whole
blocks in place, from the chaining value in `iv`, which they replace with
the one to continue from (`Cbc.next`, the last ciphertext block): a caller
may process a message in pieces of whole blocks, keeping `iv` between
calls. Padding is the caller's.

Only the pointers, `rounds` and `n` are public: no part of the chaining
value may affect timing.
-/

namespace VG.Spec.Camellia

/-- Camellia's decryption `CIPH⁻¹_K` under the subkeys `sk`, on blocks as
lists of 16 bytes (`Cbc.Cipher`). -/
def invCipher (sk : Subkeys) : Cbc.Cipher := fun b =>
  (decryptBlock sk (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- `vg_camellia_cbc_encrypt(schedule: *const [u8; 272], rounds: usize, iv: *mut [u8; 16], data: *mut [u8; 16], n: usize)`,
and `vg_camellia_cbc_decrypt` with the same signature. `rounds` is public. -/
def cbcSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]

/-- `rounds` is 18 or 24. -/
def cbcPre (pb : Nat) : Curry (cbcSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _ => rounds.toNat = 18 ∨ rounds.toNat = 24

/-- For `rounds` of 18 or 24, with the subkeys of that many rounds at
`schedule` (`subkeysAt`): replaces the `n` blocks at `data` with their CBC
encryption (§6.2) by Camellia, from the chaining value at `iv`, and the
chaining value with the last ciphertext block (unchanged if `n = 0`).
Stated for those numbers of rounds, which the precondition requires, so
that it reads only the buffers. -/
def cbcEncryptPost (pb : Nat) : cbcSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let cs := Cbc.encrypt (cipher (subkeysAt m schedule rounds.toNat)) (Aes.bytesAt m iv 16)
      (Cbc.blocksAt m data n.toNat)
    Cbc.blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs

/-- For `rounds` of 18 or 24, with the subkeys of that many rounds at
`schedule`: replaces the `n` blocks at `data` with their CBC decryption
(§6.2) by Camellia, from the chaining value at `iv`, and the chaining value
with the last ciphertext block, the last block at `data` on entry
(unchanged if `n = 0`). Stated for those numbers of rounds, as
`cbcEncryptPost`. -/
def cbcDecryptPost (pb : Nat) : cbcSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let cs := Cbc.blocksAt m data n.toNat
    Cbc.blocksAt m' data n.toNat =
        Cbc.decrypt (invCipher (subkeysAt m schedule rounds.toNat)) (Aes.bytesAt m iv 16) cs ∧
      Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs

/-- `cbcPre` and `cbcEncryptPost`. The subkeys, the chaining value and the
data are secret. -/
def cbcEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A (pre := cbcPre A.ptrBits) (post := cbcEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `cbcPre` and `cbcDecryptPost`. -/
def cbcDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A (pre := cbcPre A.ptrBits) (post := cbcDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_camellia_cbc_encrypt` on every target. -/
def cbcEncryptApi : Api where
  module := "camellia_cbc"
  name := "vg_camellia_cbc_encrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptContract A stack
  summary := "Camellia-CBC encryption (NIST SP 800-38A §6.2, RFC 3713 §2.3) of whole blocks, in \
    place: replaces the `n` 16-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, \
    where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` (leaving it unchanged if `n = 0`), so \
    that a further call continues the message. `CIPH_K` is Camellia with `rounds` rounds under \
    the subkeys at `schedule`, as `vg_camellia_expand_key` writes them. No padding is added.\n\n\
    Contract: `VG.Spec.Camellia.cbcEncryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

/-- `vg_camellia_cbc_decrypt` on every target. -/
def cbcDecryptApi : Api where
  module := "camellia_cbc"
  name := "vg_camellia_cbc_decrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptContract A stack
  summary := "Camellia-CBC decryption (NIST SP 800-38A §6.2, RFC 3713 §2.3) of whole blocks, in \
    place: replaces the `n` 16-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, \
    where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the last block at `data` on entry \
    (leaving it unchanged if `n = 0`), so that a further call continues the message. \
    `CIPH⁻¹_K` is Camellia's decryption with `rounds` rounds under the subkeys at `schedule`, \
    as `vg_camellia_expand_key` writes them. No padding is removed.\n\n\
    Contract: `VG.Spec.Camellia.cbcDecryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

end VG.Spec.Camellia
