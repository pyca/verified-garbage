import VerifiedGarbage.Spec.Camellia.Ctr
import VerifiedGarbage.Spec.Cfb

/-!
# Camellia-CFB128: the contracts, on every target

**Trusted** (as every file in `Spec/`). CFB with 128-bit segments (NIST
SP 800-38A §6.3, `Spec/Cfb.lean`, defined for any block cipher) with
Camellia's encryption (RFC 3713 §2.3, `Spec/Camellia.lean`) as `CIPH_K`, in
both directions, under the subkeys of `rounds` rounds that
`vg_camellia_expand_key` writes.

`vg_camellia_cfb128_encrypt` and `vg_camellia_cfb128_decrypt` transform `n`
whole blocks in place, from the block in `iv`, which they replace with the
one to continue from, the last ciphertext block (`Cbc.next`): a caller may
encrypt or decrypt a message in pieces of whole blocks, keeping `iv`
between calls. A partial last segment is the caller's.

Only the pointers, `rounds` and `n` are public: no part of the chaining
value may affect timing.
-/

namespace VG.Spec.Camellia

/-- `vg_camellia_cfb128_encrypt(schedule: *const [u8; 272], rounds: usize, iv: *mut [u8; 16], data: *mut [u8; 16], n: usize)`,
and `vg_camellia_cfb128_decrypt` with the same signature. `rounds` is
public. -/
def cfbSig : Sig where
  params := [("schedule", .array false .u8 272), ("rounds", .int .usize true),
    ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]

/-- `rounds` is 18 or 24. -/
def cfbPre (pb : Nat) : Curry (cfbSig.words pb) (Mem → Prop) :=
  fun _schedule rounds _iv _data _n _ => rounds.toNat = 18 ∨ rounds.toNat = 24

/-- For `rounds` of 18 or 24, with the subkeys of that many rounds at
`schedule` (`subkeysAt`): replaces the `n` blocks at `data` with their
CFB128 encryption (§6.3) by Camellia, from the block at `iv`, and that
block with the last ciphertext block (unchanged if `n = 0`). Stated for
those numbers of rounds, which the precondition requires, so that it reads
only the buffers. -/
def cfbEncryptPost (pb : Nat) : cfbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let cs := Cfb.encrypt (cipher (subkeysAt m schedule rounds.toNat)) (Aes.bytesAt m iv 16)
      (Cbc.blocksAt m data n.toNat)
    Cbc.blocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs

/-- For `rounds` of 18 or 24, with the subkeys of that many rounds at
`schedule`: replaces the `n` blocks at `data` with their CFB128 decryption
(§6.3) by Camellia, from the block at `iv`, and that block with the last
ciphertext block, the last block at `data` on entry (unchanged if `n = 0`).
Stated for those numbers of rounds, as `cfbEncryptPost`. -/
def cfbDecryptPost (pb : Nat) : cfbSig.Post pb := fun schedule rounds iv data n m m' _ =>
  (rounds.toNat = 18 ∨ rounds.toNat = 24) →
    let cs := Cbc.blocksAt m data n.toNat
    Cbc.blocksAt m' data n.toNat =
        Cfb.decrypt (cipher (subkeysAt m schedule rounds.toNat)) (Aes.bytesAt m iv 16) cs ∧
      Aes.bytesAt m' iv 16 = Cbc.next (Aes.bytesAt m iv 16) cs

/-- `cfbPre` and `cfbEncryptPost`. The subkeys, the chaining value and the
data are secret. -/
def cfbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits) (post := cfbEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `cfbPre` and `cfbDecryptPost`. -/
def cfbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits) (post := cfbDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_camellia_cfb128_encrypt` on every target. -/
def cfbEncryptApi : Api where
  module := "camellia_cfb"
  name := "vg_camellia_cfb128_encrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbEncryptContract A stack
  summary := "Camellia-CFB128 encryption (NIST SP 800-38A §6.3, with 128-bit segments; RFC \
    3713 §2.3) of whole blocks, in place: replaces the `n` 16-byte blocks `P₁ … Pₙ` at `data` \
    with `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ` \
    (leaving it unchanged if `n = 0`), so that a further call continues the message. `CIPH_K` \
    is Camellia with `rounds` rounds under the subkeys at `schedule`, as \
    `vg_camellia_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Camellia.cfbEncryptContract`. Constant time: only the pointers, \
    `rounds` and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

/-- `vg_camellia_cfb128_decrypt` on every target. -/
def cfbDecryptApi : Api where
  module := "camellia_cfb"
  name := "vg_camellia_cfb128_decrypt"
  sig := cfbSig
  writeArgs := true
  contracts := some fun A stack => cfbDecryptContract A stack
  summary := "Camellia-CFB128 decryption (NIST SP 800-38A §6.3, with 128-bit segments; RFC \
    3713 §2.3) of whole blocks, in place: replaces the `n` 16-byte blocks `C₁ … Cₙ` at `data` \
    with `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, where `C₀` is the block at `*iv`, and `*iv` with `Cₙ`, the \
    last block at `data` on entry (leaving it unchanged if `n = 0`), so that a further call \
    continues the message. `CIPH_K` is Camellia's encryption with `rounds` rounds under the \
    subkeys at `schedule`, as `vg_camellia_expand_key` writes them.\n\n\
    Contract: `VG.Spec.Camellia.cfbDecryptContract`. Constant time: only the pointers, \
    `rounds` and `n` may affect timing, not the subkeys, the chaining value or the data."
  safety := ["`rounds` must be 18 (for a key of 16 bytes) or 24 (for one of 24 or 32)."]

end VG.Spec.Camellia
