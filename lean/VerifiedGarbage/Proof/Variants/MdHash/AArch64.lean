module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha1
public import VerifiedGarbage.Proof.Sha1.AArch64.ScalarBackend
public import VerifiedGarbage.Proof.Sha1.AArch64.Sha2Backend
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha224
public import VerifiedGarbage.Proof.Sha256.AArch64.ScalarBackend
public import VerifiedGarbage.Proof.Sha256.AArch64.Sha2Backend
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
public import VerifiedGarbage.Proof.Sha512.AArch64.ScalarBackend
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha512
public import VerifiedGarbage.Proof.Sha512.AArch64.Sha3Backend

/-! # The implementations of `MdHash` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.MdHash.AArch64

def md5 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Md5.variant

def sha1 : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha1.variant Proof.Sha1.AArch64.Scalar.backend

def sha1Sha2 : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha1.variant Proof.Sha1.AArch64.Sha2.backend

def sha224 : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha224.variant Proof.Sha256.AArch64.Scalar.backend

def sha224Sha2 : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha224.variant Proof.Sha256.AArch64.Sha2.backend

def sha256 : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha256.variant Proof.Sha256.AArch64.Scalar.backend

def sha256Sha2 : Proof.Pbkdf2.Md.AArch64.MdHash :=
  Proof.Pbkdf2.Md.AArch64.Sha256.variant Proof.Sha256.AArch64.Sha2.backend

def sha384 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha384 Proof.Sha512.AArch64.Scalar.backend

def sha384Sha3 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha384 Proof.Sha512.AArch64.Sha3.backend

def sha512 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512 Proof.Sha512.AArch64.Scalar.backend

def sha512Sha3 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512 Proof.Sha512.AArch64.Sha3.backend

def sha512_224 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_224 Proof.Sha512.AArch64.Scalar.backend

def sha512_224Sha3 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_224 Proof.Sha512.AArch64.Sha3.backend

def sha512_256 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_256 Proof.Sha512.AArch64.Scalar.backend

def sha512_256Sha3 : Proof.Pbkdf2.Md.AArch64.MdHash := Proof.Pbkdf2.Md.AArch64.Sha512.sha512_256 Proof.Sha512.AArch64.Sha3.backend

/-- The implementations of MD5, best first. -/
def md5Variants := [md5]

/-- The implementations of SHA-1, best first. -/
def sha1Variants := [sha1Sha2, sha1]

/-- The implementations of SHA-224, best first. -/
def sha224Variants := [sha224Sha2, sha224]

/-- The implementations of SHA-256, best first. -/
def sha256Variants := [sha256Sha2, sha256]

/-- The implementations of SHA-384, best first. -/
def sha384Variants := [sha384Sha3, sha384]

/-- The implementations of SHA-512, best first. -/
def sha512Variants := [sha512Sha3, sha512]

/-- The implementations of SHA-512/224, best first. -/
def sha512_224Variants := [sha512_224Sha3, sha512_224]

/-- The implementations of SHA-512/256, best first. -/
def sha512_256Variants := [sha512_256Sha3, sha512_256]

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants :=
  md5Variants ++ sha1Variants ++ sha224Variants ++ sha256Variants ++ sha384Variants ++
    sha512Variants ++ sha512_224Variants ++ sha512_256Variants

end VG.Proof.Variants.MdHash.AArch64
