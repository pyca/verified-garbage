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
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha512Avx512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubAll
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512Scrub

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

open Proof.Pbkdf2.Md.X86_64.Sha512 in
/-- SHA-384 with the AVX2 compression function, whose code the residue
analysis does not follow: its streaming functions wipe every granule of
their frame (`StreamFn.scrubAuto`), as do those of SHA-512, SHA-512/224 and
SHA-512/256 with it. -/
def sha384Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha384 .avx2
    [(fin384Fn .avx2).scrubAuto (fin384Out _), (dig384Fn .avx2).scrubAuto (dig384Out _)]

def sha384ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant384

def sha512 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512

open Proof.Pbkdf2.Md.X86_64.Sha512 in
def sha512Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512 .avx2
    [(updFn .avx2).scrubAuto (updOut _), (finFn .avx2).scrubAuto (finOut _),
      (digFn .avx2).scrubAuto (digOut _)]

def sha512ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant512

def sha512_224 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512_224

open Proof.Pbkdf2.Md.X86_64.Sha512 in
def sha512_224Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_224 .avx2
    [(fin512_224Fn .avx2).scrubAuto (fin512_224Out _),
      (dig512_224Fn .avx2).scrubAuto (dig512_224Out _)]

def sha512_224ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant512_224

def sha512_256 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512_256

open Proof.Pbkdf2.Md.X86_64.Sha512 in
def sha512_256Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha512_256 .avx2
    [(fin512_256Fn .avx2).scrubAuto (fin512_256Out _),
      (dig512_256Fn .avx2).scrubAuto (dig512_256Out _)]

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
def sha384Variants := [sha384ShaNi, sha384Avx2, sha384]

/-- The implementations of SHA-512, best first. -/
def sha512Variants := [sha512ShaNi, sha512Avx2, sha512]

/-- The implementations of SHA-512/224, best first. -/
def sha512_224Variants := [sha512_224ShaNi, sha512_224Avx2, sha512_224]

/-- The implementations of SHA-512/256, best first. -/
def sha512_256Variants := [sha512_256ShaNi, sha512_256Avx2, sha512_256]

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants :=
  md5Variants ++ sha1Variants ++ sha224Variants ++ sha256Variants ++ sha384Variants ++
    sha512Variants ++ sha512_224Variants ++ sha512_256Variants

/-! ## HMAC's `init`

The implementations of `vg_hmac_<hash>_init`, best first: each variant's,
which clears its frame before returning (`MdHash.initAuto`), and over the
SHA-512 family one more, AVX2's with its two padded keys compressed at once
with AVX-512VL (`Sha512Avx512`). -/

open Proof.Pbkdf2.Md.X86_64 (InitImpl)

def md5Inits : List (InitImpl Spec.Hmac.md5I) := [md5.initAuto]

def sha1Inits : List (InitImpl Spec.Hmac.sha1I) := [sha1ShaNi.initAuto, sha1AvxBmi.initAuto, sha1.initAuto]

def sha224Inits : List (InitImpl Spec.Hmac.sha224I) := [sha224ShaNi.initAuto, sha224Avx2.initAuto, sha224.initAuto]

def sha256Inits : List (InitImpl Spec.Hmac.sha256I) := [sha256ShaNi.initAuto, sha256Avx2.initAuto, sha256.initAuto]

def sha384Inits : List (InitImpl Spec.Hmac.sha384I) :=
  [sha384ShaNi.initAuto, Sha512Avx512.init384, sha384Avx2.initAuto, sha384.initAuto]

def sha512Inits : List (InitImpl Spec.Hmac.sha512I) :=
  [sha512ShaNi.initAuto, Sha512Avx512.init512, sha512Avx2.initAuto, sha512.initAuto]

def sha512_224Inits : List (InitImpl Spec.Hmac.sha512_224I) :=
  [sha512_224ShaNi.initAuto, Sha512Avx512.init512_224, sha512_224Avx2.initAuto, sha512_224.initAuto]

def sha512_256Inits : List (InitImpl Spec.Hmac.sha512_256I) :=
  [sha512_256ShaNi.initAuto, Sha512Avx512.init512_256, sha512_256Avx2.initAuto, sha512_256.initAuto]

end VG.Proof.Variants.MdHash.X86_64
