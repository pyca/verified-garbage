module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Md5
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1AvxBmi
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha1ShaNi
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256Scrub
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha512
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha512Avx2
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha512ShaNi
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha512Avx512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubAll

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

def sha384Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512Avx2.variant384

def sha384ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant384

def sha512 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512

def sha512Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512Avx2.variant512

def sha512ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant512

def sha512_224 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512_224

def sha512_224Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512Avx2.variant512_224

def sha512_224ShaNi : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512ShaNi.variant512_224

def sha512_256 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512.variant512_256

def sha512_256Avx2 : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha512Avx2.variant512_256

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

/-! ## The streaming functions

Each variant's streaming `update` and `finalize` and one-shot `digest`, each
with what its cleanup needs (`StreamFns`; `StreamFns2` for a hash function
that shares another's `update`), in the order of the variants. -/

open Proof.Pbkdf2.Md.X86_64 (StreamFns StreamFns2)

def sha1Streams : List (StreamFns Spec.Sha1.updateApi Spec.Sha1.finalizeApi Spec.Sha1.digestApi) :=
  [Sha1ShaNi.streams, Sha1AvxBmi.streams, Sha1.streams]

def sha224Streams : List (StreamFns2 Spec.Sha256.finalize224Api Spec.Sha256.digest224Api) :=
  [Sha256ShaNi.streams224, Sha256Avx2.streams224, Sha256.streams224]

def sha256Streams : List (StreamFns Spec.Sha256.updateApi Spec.Sha256.finalizeApi Spec.Sha256.digest256Api) :=
  [Sha256ShaNi.streams, Sha256Avx2.streams, Sha256.streams]

def sha384Streams : List (StreamFns2 Spec.Sha512.finalize384Api Spec.Sha512.digest384Api) :=
  [Sha512ShaNi.streams384, Sha512Avx2.streams384, Sha512.streams384]

def sha512Streams : List (StreamFns Spec.Sha512.updateApi Spec.Sha512.finalizeApi Spec.Sha512.digest512Api) :=
  [Sha512ShaNi.streams512, Sha512Avx2.streams512, Sha512.streams512]

def sha512_224Streams : List (StreamFns2 Spec.Sha512.finalize512_224Api Spec.Sha512.digest512_224Api) :=
  [Sha512ShaNi.streams512_224, Sha512Avx2.streams512_224, Sha512.streams512_224]

def sha512_256Streams : List (StreamFns2 Spec.Sha512.finalize512_256Api Spec.Sha512.digest512_256Api) :=
  [Sha512ShaNi.streams512_256, Sha512Avx2.streams512_256, Sha512.streams512_256]

/-! ## HMAC's `init`

The implementations of `vg_hmac_<hash>_init`, best first: each variant's,
which clears its frame before returning (`MdHash.initSel`), and over the
SHA-512 family one more, AVX2's with its two padded keys compressed at once
with AVX-512VL (`Sha512Avx512`). -/

open Proof.Pbkdf2.Md.X86_64 (InitImpl)

def md5Inits : List (InitImpl Spec.Hmac.md5I) := [md5.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

def sha1Inits : List (InitImpl Spec.Hmac.sha1I) := [sha1ShaNi.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha1AvxBmi.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha1.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

def sha224Inits : List (InitImpl Spec.Hmac.sha224I) := [sha224ShaNi.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha224Avx2.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha224.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

def sha256Inits : List (InitImpl Spec.Hmac.sha256I) := [sha256ShaNi.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha256Avx2.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha256.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

def sha384Inits : List (InitImpl Spec.Hmac.sha384I) :=
  [sha384ShaNi.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), Sha512Avx512.init384, sha384Avx2.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha384.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

def sha512Inits : List (InitImpl Spec.Hmac.sha512I) :=
  [sha512ShaNi.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), Sha512Avx512.init512, sha512Avx2.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha512.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

def sha512_224Inits : List (InitImpl Spec.Hmac.sha512_224I) :=
  [sha512_224ShaNi.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), Sha512Avx512.init512_224, sha512_224Avx2.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha512_224.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

def sha512_256Inits : List (InitImpl Spec.Hmac.sha512_256I) :=
  [sha512_256ShaNi.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), Sha512Avx512.init512_256, sha512_256Avx2.initSel .avx [] (by decide) (by decide) (by lit_decide) (by lit_decide), sha512_256.initSel .sse [] (by decide) (by decide) (by lit_decide) (by lit_decide)]

/-! ## HMAC's `finalize`

Each variant's HMAC `finalize`, with what its cleanup needs (`FinImpl`), in
the order of the variants. -/

open Proof.Pbkdf2.Md.X86_64 (FinImpl)

def md5Fins : List FinImpl := [Proof.Pbkdf2.Md.X86_64.Md5.fin]

def sha1Fins : List FinImpl := [Sha1ShaNi.fin, Sha1AvxBmi.fin, Sha1.fin]

def sha224Fins : List FinImpl := [Sha256ShaNi.fin224, Sha256Avx2.fin224, Sha256.fin224]

def sha256Fins : List FinImpl := [Sha256ShaNi.fin, Sha256Avx2.fin, Sha256.fin]

def sha384Fins : List FinImpl := [Sha512ShaNi.fin384, Sha512Avx2.fin384, Sha512.fin384]

def sha512Fins : List FinImpl := [Sha512ShaNi.fin512, Sha512Avx2.fin512, Sha512.fin512]

def sha512_224Fins : List FinImpl := [Sha512ShaNi.fin512_224, Sha512Avx2.fin512_224, Sha512.fin512_224]

def sha512_256Fins : List FinImpl := [Sha512ShaNi.fin512_256, Sha512Avx2.fin512_256, Sha512.fin512_256]

/-! ## PBKDF2's `pbkdf2`

Each variant's PBKDF2, with what its cleanup needs (`Pbkdf2Impl`), in the
order of the variants. -/

open Proof.Pbkdf2.Md.X86_64 (Pbkdf2Impl)

def md5Pbkdf2s : List Pbkdf2Impl := [⟨md5, .sse, by lit_decide⟩]

def sha1Pbkdf2s : List Pbkdf2Impl := [⟨sha1ShaNi, .sse, by lit_decide⟩, ⟨sha1AvxBmi, .avx, by lit_decide⟩, ⟨sha1, .sse, by lit_decide⟩]

def sha224Pbkdf2s : List Pbkdf2Impl := [⟨sha224ShaNi, .sse, by lit_decide⟩, ⟨sha224Avx2, .avx, by lit_decide⟩, ⟨sha224, .sse, by lit_decide⟩]

def sha256Pbkdf2s : List Pbkdf2Impl := [⟨sha256ShaNi, .sse, by lit_decide⟩, ⟨sha256Avx2, .avx, by lit_decide⟩, ⟨sha256, .sse, by lit_decide⟩]

def sha384Pbkdf2s : List Pbkdf2Impl := [⟨sha384ShaNi, .avx, by lit_decide⟩, ⟨sha384Avx2, .avx, by lit_decide⟩, ⟨sha384, .sse, by lit_decide⟩]

def sha512Pbkdf2s : List Pbkdf2Impl := [⟨sha512ShaNi, .avx, by lit_decide⟩, ⟨sha512Avx2, .avx, by lit_decide⟩, ⟨sha512, .sse, by lit_decide⟩]

def sha512_224Pbkdf2s : List Pbkdf2Impl := [⟨sha512_224ShaNi, .avx, by lit_decide⟩, ⟨sha512_224Avx2, .avx, by lit_decide⟩, ⟨sha512_224, .sse, by lit_decide⟩]

def sha512_256Pbkdf2s : List Pbkdf2Impl := [⟨sha512_256ShaNi, .avx, by lit_decide⟩, ⟨sha512_256Avx2, .avx, by lit_decide⟩, ⟨sha512_256, .sse, by lit_decide⟩]

end VG.Proof.Variants.MdHash.X86_64
