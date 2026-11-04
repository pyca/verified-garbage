module

public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Spec.RsaPss.Table

/-!
# EMSA-PSS's encoding and its check with the hash functions as tables, as functions

Not trusted: the contracts of internal functions, which only verified code
calls (`vg_rsa_pss_sign` and `vg_rsa_pss_verify_precomputed` on AArch64),
that their proofs and their callers' compose. As
`Proof/RsaPss/EncodingContract.lean`'s, with two last parameters, `hash`, a
table of `MdHash`, and `mgf1`, a table of `Hash` (`Spec/RsaPss/Table.lean`),
for the hash function of index `i` in `Mgf1.hashes`: the table `hash` names
it (its index is `i`), and the digest is its length. Each of `encode` and
`checkEncoding` has one copy for each index, which the callers choose by the
table's index. Their working space is 1088 words (`encScratch`): MGF1's
works at an offset in it.
-/

@[expose] public section

namespace VG.Proof.RsaPss

open VG.Spec VG.Spec.RsaPss
open VG.Spec.Rsa (bytesAt)

/-- The digest length of the hash function of index `i`. -/
def hashLen (i : Nat) : Nat := (Mgf1.hashes[i]?.map (·.len)).getD 0

/-- The 64-bit words of working space `encode` and `checkEncoding` use. -/
def encScratch : Nat := 1088

/-- The index in the table of `MdHash` at `p`, the table's first word of
data. -/
def tabIdx (m : Mem) (p : Addr) : Nat := (m.readW (p + BitVec.ofNat 64 (64 / 8 * MdHashTable.fns)) 64).toNat

/-! ## `vg_rsa_pss_encode_<H>` -/

/-- `encode(em: *mut u8, em_len: usize, digest: *const [u8; hLen],
salt: *const u8, salt_len: usize, em_bits: usize, scratch: *mut u64,
scratch_len: usize, hash: *const [usize; 11], mgf1: *const [usize; 5]) -> u32`. -/
def encodeTSig (D : Nat) : Sig where
  params := [("em", .slice true .u8 "em_len"), ("digest", .array false .u8 D),
    ("salt", .slice false .u8 "salt_len"), ("em_bits", .int .usize true),
    ("scratch", .slice true .u64 "scratch_len"), ("hash", MdHashTable.param), ("mgf1", HashTable.param)]
  ret := some .u32

/-- `encode` of the digest with the salt into `em_bits` bits, with the hash
functions of the tables, of which `hash` has the index `i`. -/
def encodeTContract (i : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encodeTSig (hashLen i)).contract A
    (pre := fun _em emLen _digest _salt _saltLen emBits _scratch scratchLen hash _mgf1 m =>
      1 ≤ emBits.toNat ∧ emBits.toNat ≤ maxEmBits ∧ emLen.toNat = emLength emBits.toNat ∧
        encScratch ≤ scratchLen.toNat ∧ tabIdx m hash = i)
    (post := fun em emLen digest salt saltLen emBits _scratch _scratchLen hash mgf1 m m' r =>
      ∀ H G, MdHashTable.hashAt 64 m hash = some H → HashTable.hashAt 64 m mgf1 = some G →
        match encode H G (bytesAt m digest H.len) (bytesAt m salt saltLen.toNat) emBits.toNat with
        | some e => r = 1 ∧ bytesAt m' em emLen.toNat = e
        | none => r = 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _em _emLen _digest _salt _saltLen _emBits _scratch _scratchLen _hash _mgf1 _m => [])

/-! ## `vg_rsa_pss_check_encoding_<H>` -/

/-- `check_encoding(digest: *const [u8; hLen], em: *const u8, em_len: usize,
em_bits: usize, salt_len: usize, any_salt_len: u32, scratch: *mut u64,
scratch_len: usize, hash: *const [usize; 11], mgf1: *const [usize; 5]) -> u32`. -/
def checkEncodingTSig (D : Nat) : Sig where
  params := [("digest", .array false .u8 D), ("em", .slice false .u8 "em_len"),
    ("em_bits", .int .usize true), ("salt_len", .int .usize true),
    ("any_salt_len", .int .u32 true), ("scratch", .slice true .u64 "scratch_len"),
    ("hash", MdHashTable.param), ("mgf1", HashTable.param)]
  ret := some .u32

/-- `verifyEncoding` of the encoding for the digest, with the hash functions
of the tables, of which `hash` has the index `i`. -/
def checkEncodingTContract (i : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (checkEncodingTSig (hashLen i)).contract A
    (pre := fun _digest _em emLen emBits _saltLen _anySaltLen _scratch scratchLen hash _mgf1 m =>
      1 ≤ emBits.toNat ∧ emBits.toNat ≤ maxEmBits ∧ emLen.toNat = emLength emBits.toNat ∧
        encScratch ≤ scratchLen.toNat ∧ tabIdx m hash = i)
    (post := fun digest em emLen emBits saltLen anySaltLen _scratch _scratchLen hash mgf1 m _m' r =>
      ∀ H G, MdHashTable.hashAt 64 m hash = some H → HashTable.hashAt 64 m mgf1 = some G →
        r = if verifyEncoding H G (bytesAt m digest H.len) (bytesAt m em emLen.toNat)
            emBits.toNat (expectedSaltLen saltLen anySaltLen) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _digest _em _emLen _emBits _saltLen _anySaltLen _scratch _scratchLen _hash _mgf1 _m => [])

end VG.Proof.RsaPss
