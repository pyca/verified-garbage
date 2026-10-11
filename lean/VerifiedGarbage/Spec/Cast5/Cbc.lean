import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Spec.Cbc

/-!
# CAST5-CBC: the contracts, on every target

**Trusted** (as every file in `Spec/`). CBC (NIST SP 800-38A §6.2,
`Spec/Cbc.lean`, defined for any block cipher) with CAST5 (RFC 2144 §2,
`Spec/Cast5.lean`): its encryption as `CIPH_K` and its decryption as
`CIPH⁻¹_K`, on 8-byte blocks, under the subkeys that `vg_cast5_expand_key`
writes, with `rounds` rounds.

`vg_cast5_cbc_encrypt` and `vg_cast5_cbc_decrypt` transform `n` whole blocks
in place, from the chaining value at `iv`, which they only read. A caller may
process a message in pieces of whole blocks: the chaining value of the next
piece is the last ciphertext block of this one (`Cbc.next`), which the caller
has (after encryption, the last block at `data`; before decryption, the last
block it decrypts). Padding is the caller's.

Only the pointers, `rounds` and `n` are public: no part of the chaining value
may affect timing.
-/

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

/-- `vg_cast5_cbc_encrypt(schedule: *const [u8; 128], rounds: usize, iv: *const [u8; 8], data: *mut [u8; 8], n: usize)`,
and `vg_cast5_cbc_decrypt` with the same signature. `rounds` is public, 12
or 16 (the precondition). -/
def cbcSig : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("iv", .array false .u8 8), ("data", .slice true (.array .u8 8) "n")]

/-- `rounds` is 12 or 16. -/
def cbcPre (pb : Nat) : Curry (cbcSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their CBC encryption (§6.2) by CAST5, from the
chaining value at `iv`. -/
def cbcEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A (pre := cbcPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      cbcBlocksAt m' data n.toNat =
        Cbc.encrypt (cipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their CBC decryption (§6.2) by CAST5, from the
chaining value at `iv`. -/
def cbcDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcSig.contract A (pre := cbcPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      cbcBlocksAt m' data n.toNat =
        Cbc.decrypt (invCipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat))
    (writeArgs := true) (stack := stack)

/-- `vg_cast5_cbc_encrypt` on every target. -/
def cbcEncryptApi : Api where
  module := "cast5_cbc"
  name := "vg_cast5_cbc_encrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcEncryptContract A stack
  summary := "CAST5-CBC encryption (NIST SP 800-38A §6.2, RFC 2144 §2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `P₁ … Pₙ` at `data` with `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, where \
    `C₀` is the block at `*iv`, which is only read: a further call continues the message \
    from `Cₙ`, the last block at `data` on return. `CIPH_K` is CAST-128 encryption with \
    `rounds` rounds under the subkeys written by `vg_cast5_expand_key`. No padding is added.\n\n\
    Contract: `VG.Spec.Cast5.cbcEncryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

/-- `vg_cast5_cbc_decrypt` on every target. -/
def cbcDecryptApi : Api where
  module := "cast5_cbc"
  name := "vg_cast5_cbc_decrypt"
  sig := cbcSig
  writeArgs := true
  contracts := some fun A stack => cbcDecryptContract A stack
  summary := "CAST5-CBC decryption (NIST SP 800-38A §6.2, RFC 2144 §2) of whole blocks, in place: \
    replaces the `n` 8-byte blocks `C₁ … Cₙ` at `data` with `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`, \
    where `C₀` is the block at `*iv`, which is only read: a further call continues the \
    message from `Cₙ`, the last block at `data` on entry. `CIPH⁻¹_K` is CAST-128 decryption \
    with `rounds` rounds under the subkeys written by `vg_cast5_expand_key`. No padding is \
    removed.\n\n\
    Contract: `VG.Spec.Cast5.cbcDecryptContract`. Constant time: only the pointers, `rounds` \
    and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 12 (for a key of up to 10 bytes) or 16 (for a longer one)."]

end VG.Spec.Cast5
