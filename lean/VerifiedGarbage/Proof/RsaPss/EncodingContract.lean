module

public import VerifiedGarbage.Spec.RsaPss.Contract

/-!
# EMSA-PSS encoding and its check, as functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

The two halves of RSASSA-PSS that
use the hash functions, `encode` (EMSA-PSS-ENCODE, RFC 8017 §9.1.1) and
`verifyEncoding` (EMSA-PSS-VERIFY, §9.1.2), as functions of their own, so
that signing and verification can call them around the RSA primitive.

A function that calls functions with variants has one copy for each of
their implementations it can reach: today every RSA-PSS function is
copied for each implementation of its hash function times each of the RSA
primitive's (on x86-64, base, `adx` and `ifma`). With these two functions,
only they depend on the hash function's implementation, and signing and
verification shrink to calls. The contracts of `sign` and `verify` are
unchanged: they still state the whole of RSASSA-PSS.

Both are constant time but for the lengths: the digest, the salt and the
encoding are secret (an encoding checked during verification is the RSA
result of a signature that may be chosen to probe it).
-/

@[expose] public section

namespace VG.Proof.RsaPss

open VG.Spec VG.Spec.RsaPss
open VG.Spec.Mgf1 (Hash)
open VG.Spec.Rsa (bytesAt)

variable (H G : Hash)

/-- The 64-bit words of working space the encoding functions use. -/
def encodingScratchWords : Nat := 1024

/-- The most bits of an encoding: that of a modulus of 8192 bits. -/
def maxEmBits : Nat := 8191

/-! ## `vg_rsa_pss_<H>_mgf1_<G>_encode` -/

/-- `vg_rsa_pss_<H>_mgf1_<G>_encode(em: *mut u8, em_len: usize,
digest: *const [u8; hLen], salt: *const u8, salt_len: usize, em_bits: usize,
scratch: *mut u64, scratch_len: usize) -> u32`. -/
def encodeSig : Sig where
  params := [("em", .slice true .u8 "em_len"), ("digest", .array false .u8 H.len),
    ("salt", .slice false .u8 "salt_len"), ("em_bits", .int .usize true),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- `encode` of the digest with the salt into `em_bits` bits: 1 with the
`em_len = ⌈em_bits / 8⌉` octets of the encoding at `em`, or 0 if it fails
(the salt does not fit). Constant time but for the lengths. -/
def encodeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encodeSig H).contract A
    (pre := fun _em emLen _digest _salt _saltLen emBits _scratch scratchLen _ =>
      1 ≤ emBits.toNat ∧ emBits.toNat ≤ maxEmBits ∧ emLen.toNat = emLength emBits.toNat ∧
        encodingScratchWords ≤ scratchLen.toNat)
    (post := fun em emLen digest salt saltLen emBits _scratch _scratchLen m m' r =>
      match encode H G (bytesAt m digest H.len) (bytesAt m salt saltLen.toNat) emBits.toNat with
      | some e => r = 1 ∧ bytesAt m' em emLen.toNat = e
      | none => r = 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _em _emLen _digest _salt _saltLen _emBits _scratch _scratchLen _m => [])

/-! ## `vg_rsa_pss_<H>_mgf1_<G>_check_encoding` -/

/-- `vg_rsa_pss_<H>_mgf1_<G>_check_encoding(digest: *const [u8; hLen],
em: *const u8, em_len: usize, em_bits: usize, salt_len: usize,
any_salt_len: u32, scratch: *mut u64, scratch_len: usize) -> u32`. -/
def checkEncodingSig : Sig where
  params := [("digest", .array false .u8 H.len), ("em", .slice false .u8 "em_len"),
    ("em_bits", .int .usize true), ("salt_len", .int .usize true),
    ("any_salt_len", .int .u32 true), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

/-- `verifyEncoding` of the `em_len = ⌈em_bits / 8⌉` octets at `em` for the
digest, expecting the salt length `expectedSaltLen salt_len any_salt_len`:
1 if the encoding is consistent and 0 otherwise. Constant time but for the
lengths. -/
def checkEncodingContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (checkEncodingSig H).contract A
    (pre := fun _digest _em emLen emBits _saltLen _anySaltLen _scratch scratchLen _ =>
      1 ≤ emBits.toNat ∧ emBits.toNat ≤ maxEmBits ∧ emLen.toNat = emLength emBits.toNat ∧
        encodingScratchWords ≤ scratchLen.toNat)
    (post := fun digest em emLen emBits saltLen anySaltLen _scratch _scratchLen m _m' r =>
      r = if verifyEncoding H G (bytesAt m digest H.len) (bytesAt m em emLen.toNat)
          emBits.toNat (expectedSaltLen saltLen anySaltLen) then 1 else 0)
    (stack := stack)
    (leak := some fun _digest _em _emLen _emBits _saltLen _anySaltLen _scratch _scratchLen _m =>
      [])

end VG.Proof.RsaPss
