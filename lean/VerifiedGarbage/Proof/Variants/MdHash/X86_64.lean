module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1AvxBmi
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1ShaNi
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha224
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha512
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha512ShaNi

/-! # The implementations of `MdHash` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64

def md5 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Pbkdf2.Md.X86_64.Md5.variant

def sha1 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha1.variant

def sha1AvxBmi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha1AvxBmi.variant

def sha1ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha1ShaNi.variant

def sha224 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256.variant224

def sha224Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256Avx2.variant224

def sha224ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256ShaNi.variant224

def sha256 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256.variant

open VG.Impl.Sha256.X86_64.Stream (Callee) in
def sha256Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256Avx2.variant

def sha256ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256ShaNi.variant

def sha384 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant384

def sha384Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha384 .avx2 (Proof.Pbkdf2.Md.X86_64.Sha512.stream384 .avx2)

def sha384Avx512 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha512.sha384 .avx512 with initScrub := true, initOnly := true }

def sha384ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant384

def sha512 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512

def sha512Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 .avx2 (Proof.Pbkdf2.Md.X86_64.Sha512.stream .avx2)

def sha512Avx512 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha512.sha512 .avx512 with initScrub := true, initOnly := true }

def sha512ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant512

def sha512_224 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512_224

def sha512_224Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_224 .avx2 (Proof.Pbkdf2.Md.X86_64.Sha512.stream512_224 .avx2)

def sha512_224Avx512 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha512.sha512_224 .avx512 with initScrub := true, initOnly := true }

def sha512_224ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant512_224

def sha512_256 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512_256

def sha512_256Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 .avx2 (Proof.Pbkdf2.Md.X86_64.Sha512.stream512_256 .avx2)

def sha512_256Avx512 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  { Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 .avx512 with initScrub := true, initOnly := true }

def sha512_256ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant512_256

/-- The implementations of MD5, best first. -/
def md5Variants := [md5]

/-- The implementations of SHA-1, best first. -/
def sha1Variants := [sha1ShaNi, sha1AvxBmi, sha1]

/-- The implementations of SHA-224, best first. -/
def sha224Variants := [sha224ShaNi, sha224Avx2, sha224]

/-- The implementations of SHA-256, best first. -/
def sha256Variants := [sha256ShaNi, sha256Avx2, sha256]

/-- The implementations of SHA-384, best first. -/
def sha384Variants := [sha384ShaNi, sha384Avx512, sha384Avx2, sha384]

/-- The implementations of SHA-512, best first. -/
def sha512Variants := [sha512ShaNi, sha512Avx512, sha512Avx2, sha512]

/-- The implementations of SHA-512/224, best first. -/
def sha512_224Variants := [sha512_224ShaNi, sha512_224Avx512, sha512_224Avx2, sha512_224]

/-- The implementations of SHA-512/256, best first. -/
def sha512_256Variants := [sha512_256ShaNi, sha512_256Avx512, sha512_256Avx2, sha512_256]

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants :=
  md5Variants ++ sha1Variants ++ sha224Variants ++ sha256Variants ++ sha384Variants ++
    sha512Variants ++ sha512_224Variants ++ sha512_256Variants

end VG.Proof.Variants.MdHash.X86_64
