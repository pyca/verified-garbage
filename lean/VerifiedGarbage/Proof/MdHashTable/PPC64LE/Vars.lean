module

public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Proof.Sha512.Md

-- separate module: the variants, with the hash functions' own modules, which only the instances import

/-!
# The variants of the tables of `MdHash` on PPC64LE

Untrusted: everything here is checked by Lean. One variant of each hash
function of `Spec.Mgf1.hashes` (`mvars`): its streaming functions as
RSAES-OAEP has them, its family of streaming code, and its `Md`'s link to
the hash function of the specification from its initial hash value, as
PBKDF2's on PPC64LE.
-/

@[expose] public section

namespace VG.Proof.MdHashTable.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE

def md5M : MVar where
  H := Md5.hash
  l := Proof.RsaOaep.PPC64LE.md5L
  idx := rfl
  F := md5F
  iv := Spec.Md5.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha1M : MVar where
  H := Sha1.hash
  l := Proof.RsaOaep.PPC64LE.sha1L
  idx := rfl
  F := sha1F
  iv := Spec.Sha1.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha224M : MVar where
  H := Sha224.hash
  l := Proof.RsaOaep.PPC64LE.sha224L
  idx := rfl
  F := sha256F
  iv := Spec.Sha256.H0_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => (Proof.Sha256.sha224_eq m).symm, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha256M : MVar where
  H := Sha256.hash
  l := Proof.RsaOaep.PPC64LE.sha256L
  idx := rfl
  F := sha256F
  iv := Spec.Sha256.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha384M : MVar where
  H := Sha384.hash
  l := Proof.RsaOaep.PPC64LE.sha384L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_384
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512M : MVar where
  H := Sha512.hash
  l := Proof.RsaOaep.PPC64LE.sha512L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m =>
    (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512_224M : MVar where
  H := Sha512_224.hash
  l := Proof.RsaOaep.PPC64LE.sha512_224L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512_256M : MVar where
  H := Sha512_256.hash
  l := Proof.RsaOaep.PPC64LE.sha512_256L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512_256
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

/-- Every hash function's variant. -/
def mvars : List MVar := [md5M, sha1M, sha224M, sha256M, sha384M, sha512M, sha512_224M, sha512_256M]

end VG.Proof.MdHashTable.PPC64LE
