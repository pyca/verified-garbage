module

public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.Spec.Cast5
public import VerifiedGarbage.TCB.Artifact

/-!
# CAST5-CBC: the contracts, on every target

**Trusted** (as every file in `Spec/`). CBC (NIST SP 800-38A §6.2,
`Spec/Cbc.lean`, defined for any block cipher) with CAST5 (RFC 2144 §2,
`Spec/Cast5.lean`): its encryption as `CIPH_K` and its decryption as
`CIPH⁻¹_K`, on 8-byte blocks, under the subkeys that `vg_cast5_expand_key`
writes, with `rounds` rounds.

`vg_cast5_cbc_encrypt_chained` and `vg_cast5_cbc_decrypt_chained` transform
`n` whole blocks in place, from the chaining value at `iv`, which they
replace with the chaining value to continue from (`Cbc.next`, the last
ciphertext block), as AES-CBC's functions do (`Spec/Cbc/Contract.lean`):
a caller may process a message in pieces of whole blocks, and keeps no
block of its own between them. Padding is the caller's.

Only the pointers, `rounds` and `n` are public: no part of the chaining value
may affect timing.
-/

@[expose] public section

namespace VG.Spec.Cast5

/-- CAST-128 encryption `CIPH_K` under the subkeys `k` with `n` rounds, on
blocks as lists of 8 bytes (`Cbc.Cipher`). -/
def cipher (k : Schedule) (n : Nat) : Cbc.Cipher := fun b =>
  (encryptBlock k n (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- CAST-128 decryption `CIPH⁻¹_K` under the subkeys `k` with `n` rounds, on
blocks as lists of 8 bytes. -/
def invCipher (k : Schedule) (n : Nat) : Cbc.Cipher := fun b =>
  (decryptBlock k n (Vector.ofFn fun i => b.getD i.val 0)).toList

/-- The `n` 8-byte blocks at `p`, as lists of bytes. -/
def cbcBlocksAt (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (blocksAt m p n).map Vector.toList

/-- `vg_cast5_cbc_encrypt_chained(schedule: *const [u8; 128], rounds: usize, iv: *mut [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_cast5_cbc_decrypt_chained` with the same signature. -/
def cbcChainedSig : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("iv", .array true .u8 8), ("data", .slice true (.array .u8 8) "n")]

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the
`n` blocks at `data` with their CBC encryption (§6.2) by CAST5, from the
chaining value at `iv`, and the chaining value with the last ciphertext
block (unchanged if `n = 0`), as `Cbc.aesEncryptContract` does. -/
def cbcEncryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (pre := fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := Cbc.encrypt (cipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8)
        (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧
        Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the
`n` blocks at `data` with their CBC decryption (§6.2) by CAST5, from the
chaining value at `iv`, and the chaining value with the last ciphertext
block, the last block at `data` on entry (unchanged if `n = 0`), as
`Cbc.aesDecryptContract` does. -/
def cbcDecryptChainedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (pre := fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat =
          Cbc.decrypt (invCipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) cs ∧
        Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- `vg_cast5_cbc_encrypt_chained` on every target. -/
def cbcEncryptChainedApi : Api where
  module := "cast5_cbc"
  name := "vg_cast5_cbc_encrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptChainedContract A stack
  summary := "CAST5-CBC encryption (NIST SP 800-38A §6.2, RFC 2144 §2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, where `C₀` \
    is the block at `*iv`, and `*iv` with `Cₙ` (leaving it unchanged if `n = 0`), so that a \
    further call continues the message. `CIPH_K` is CAST-128 encryption with `rounds` rounds under \
    the subkeys written by `vg_cast5_expand_key`. No padding is added.\n\n\
    Contract: `VG.Spec.Cast5.cbcEncryptChainedContract`. Constant time: only the pointers, \
    `rounds` and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

/-- `vg_cast5_cbc_decrypt_chained` on every target. -/
def cbcDecryptChainedApi : Api where
  module := "cast5_cbc"
  name := "vg_cast5_cbc_decrypt_chained"
  sig := cbcChainedSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptChainedContract A stack
  summary := "CAST5-CBC decryption (NIST SP 800-38A §6.2, RFC 2144 §2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, where `C₀` \
    is the block at `*iv`, and `*iv` with `Cₙ`, the last block at `data` on entry (leaving it \
    unchanged if `n = 0`), so that a further call continues the message. `CIPH⁻¹_K` is CAST-128 \
    decryption with `rounds` rounds under the subkeys written by `vg_cast5_expand_key`. No padding \
    is removed.\n\n\
    Contract: `VG.Spec.Cast5.cbcDecryptChainedContract`. Constant time: only the pointers, \
    `rounds` and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

end VG.Spec.Cast5
