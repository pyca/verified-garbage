module

public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Impl.Pbkdf2.Md.Arm
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.Arm
public import VerifiedGarbage.Impl.Md5.Arm.Stream
public import VerifiedGarbage.Impl.Sha1.Arm.Stream
public import VerifiedGarbage.Impl.Sha256.Arm.Stream
public import VerifiedGarbage.Impl.Sha512.Arm.Stream
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# HMAC and PBKDF2 on ARMv7, for each hash function, as emitted

The generic code of HMAC's `init` and `finalize` and of PBKDF2
(`Impl/Pbkdf2/Md/Arm.lean`, `Impl/Pbkdf2/Whole/Arm.lean`,
`Impl/Pbkdf2/Md/AnyKey/Arm.lean`) at each hash function: the hash function as
that code calls it (`md5Md`, `sha1Md`, …, an `Impl.Pbkdf2.Md.Arm.Hash`: its
streaming functions, `Impl.<Hash>.Arm.Stream.streamFns`, its hash value,
length field, digest code and compression function), the functions PBKDF2
calls for it (`fnsOf`), and the frames that hold each function's working
space (`frame`, `anyFrame`, `pbkFrame`, each rounded up to a multiple of 32
bytes, which an ARM immediate encodes).

`Fn` is each function as emitted: its code, then its cleanup
(`Impl/Residue/Arm.lean`), the stack its contract reserves zeroed and the
registers a callee may change set to constants. None returns a value. The
stack is `24 + anyFrame I` for HMAC's `init` and `24 + pbkFrame I` for
PBKDF2, each rounded up to a multiple of 32 bytes (a frame size of the
model), and `16 + frame I` for HMAC's `finalize`.
-/

@[expose] public section

namespace VG.Impl.Hmac.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Impl.Pbkdf2.Whole.Arm (Fns)

/-! ## The hash functions -/

/-- MD5: a 16-byte hash value, a little-endian length field, and
`vg_md5_compress`, with 64 bytes of scratch space. -/
def md5Md : Hash where
  st := Impl.Md5.Arm.Stream.streamFns
  N := 16
  L := 8
  be := false
  so := 64
  out := Impl.Md5.Arm.Stream.params.out
  compN := "vg_md5_compress"
  compC := Impl.Md5.Arm.compress

/-- SHA-1: a 20-byte hash value, a big-endian length field, and
`vg_sha1_compress`, with 112 bytes of scratch space. -/
def sha1Md : Hash where
  st := Impl.Sha1.Arm.Stream.streamFns
  N := 20
  L := 8
  be := true
  so := 112
  out := Impl.Sha1.Arm.Stream.params.out
  compN := "vg_sha1_compress"
  compC := Impl.Sha1.Arm.compress

/-- SHA-224: SHA-256's 32-byte hash value, big-endian length field and
`vg_sha256_compress`, with 112 bytes of scratch space. -/
def sha224Md : Hash where
  st := Impl.Sha256.Arm.Stream.streamFns224
  N := 32
  L := 8
  be := true
  so := 112
  out := Impl.Sha256.Arm.Stream.params.out
  compN := "vg_sha256_compress"
  compC := Impl.Sha256.Arm.compress

/-- SHA-256: a 32-byte hash value, a big-endian length field and
`vg_sha256_compress`, with 112 bytes of scratch space. -/
def sha256Md : Hash where
  st := Impl.Sha256.Arm.Stream.streamFns
  N := 32
  L := 8
  be := true
  so := 112
  out := Impl.Sha256.Arm.Stream.params.out
  compN := "vg_sha256_compress"
  compC := Impl.Sha256.Arm.compress

/-- The member of the SHA-512 family with a `D`-byte digest, initial hash
value `iv` and streaming `init` named `initN`: a 64-byte hash value, a
16-byte big-endian length field, and `vg_sha512_compress`, with 224 bytes of
scratch space. -/
def sha512Md (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  st := Impl.Sha512.Arm.Stream.streamFnsOf D initN iv
  N := 64
  L := 16
  be := true
  so := 224
  out := (List.range 8).flatMap Impl.Sha512.Arm.Stream.outW
  compN := "vg_sha512_compress"
  compC := Impl.Sha512.Arm.compress

def sha384Md : Hash := sha512Md 48 "vg_sha384_init_core" Spec.Sha512.H0_384
def sha512Md' : Hash := sha512Md 64 "vg_sha512_init_core" Spec.Sha512.H0_512
def sha512_224Md : Hash := sha512Md 28 "vg_sha512_224_init_core" Spec.Sha512.H0_512_224
def sha512_256Md : Hash := sha512Md 32 "vg_sha512_256_init_core" Spec.Sha512.H0_512_256

/-! ## PBKDF2's functions -/

/-- The functions `pbkdf2` calls for the hash function `M` of the instance
`I` (`Impl/Pbkdf2/Md/Arm.lean`), with the working space of `I`'s functions,
by the names they are registered with. -/
def fnsOf (I : Spec.Hmac.Instance) (M : Hash) : Fns where
  H := M.st
  W := I.scratch
  hiN := s!"vg_hmac_{I.rust}_init_scratch"
  hiC := M.hmacInit
  hfN := s!"vg_hmac_{I.rust}_finalize_scratch"
  hfC := M.hmacFin
  itN := s!"vg_pbkdf2_hmac_{I.rust}_iterate"
  itC := M.iterate

def md5F : Fns := fnsOf Spec.Hmac.md5I md5Md
def sha1F : Fns := fnsOf Spec.Hmac.sha1I sha1Md
def sha224F : Fns := fnsOf Spec.Hmac.sha224I sha224Md
def sha256F : Fns := fnsOf Spec.Hmac.sha256I sha256Md
def sha384F : Fns := fnsOf Spec.Hmac.sha384I sha384Md
def sha512F : Fns := fnsOf Spec.Hmac.sha512I sha512Md'
def sha512_224F : Fns := fnsOf Spec.Hmac.sha512_224I sha512_224Md
def sha512_256F : Fns := fnsOf Spec.Hmac.sha512_256I sha512_256Md

/-! ## The frames -/

/-- The bytes of `init`'s and `finalize`'s frames: `finalize`'s copy of its
one stack argument, the saved registers and the working space, rounded up to
a multiple of 32. -/
def frame (I : Spec.Hmac.Instance) : Nat := (4 + 8 + 8 * I.scratch + 31) / 32 * 32

/-- The bytes of `init`'s frame for a key of any length: the saved registers
and the working space, rounded up to a multiple of 32. -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := (8 + 8 * I.initAnyKeyScratch + 31) / 32 * 32

/-- The bytes of `pbkdf2`'s frame: its copy of its three stack arguments, the
saved registers and the working space, rounded up to a multiple of 32. -/
def pbkFrame (I : Spec.Hmac.Instance) : Nat := (12 + 8 + 8 * I.pbkdf2Scratch + 31) / 32 * 32

/-! ## The functions -/

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`, of instance
`I`: for a key of at most a block, `init_scratch` (`hmacInit`) in a frame
holding its working space; for a longer key (cold), `F.hmacInitAny`, in a
frame holding its larger working space, which it wipes. -/
def initCode (I : Spec.Hmac.Instance) (hmacInit : Prog isa) (F : Fns) : Prog isa :=
  Impl.Pbkdf2.Whole.Arm.initEntry I.S.H.blockSize
    (Impl.StackScratch.Arm.withStackScratch (frame I) 0 hmacInit)
    (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame I) 0 (2 * I.initAnyKeyScratch) F.hmacInitAny)

/-- HMAC's `finalize`, `vg_hmac_<hash>_finalize`: `finalize_scratch`
(`hmacFin`) in a frame holding its working space. -/
def finCode (I : Spec.Hmac.Instance) (M : Hash) : Prog isa :=
  Impl.StackScratch.Arm.withStackScratch (frame I) 1 M.hmacFin

/-- PBKDF2, `vg_pbkdf2_hmac_<hash>`: `pbkdf2_scratch` in a frame holding its
working space. -/
def pbkdf2Code (I : Spec.Hmac.Instance) (F : Fns) : Prog isa :=
  Impl.StackScratch.Arm.withStackScratch (pbkFrame I) 3 F.pbkdf2

end VG.Impl.Hmac.Stream.Arm

namespace VG.Impl.Hmac.Stream.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.Hmac.Stream.Arm

/-- `vg_hmac_md5_init`. -/
def initMd5 : Prog isa := scrubF 0 1088 (initCode Spec.Hmac.md5I md5Md.hmacInit md5F)
/-- `vg_hmac_sha1_init`. -/
def initSha1 : Prog isa := scrubF 0 1184 (initCode Spec.Hmac.sha1I sha1Md.hmacInit sha1F)
/-- `vg_hmac_sha224_init`. -/
def initSha224 : Prog isa := scrubF 0 1664 (initCode Spec.Hmac.sha224I sha224Md.hmacInit sha224F)
/-- `vg_hmac_sha256_init`. -/
def initSha256 : Prog isa := scrubF 0 1664 (initCode Spec.Hmac.sha256I sha256Md.hmacInit sha256F)
/-- `vg_hmac_sha384_init`. -/
def initSha384 : Prog isa := scrubF 0 3456 (initCode Spec.Hmac.sha384I sha384Md.hmacInit sha384F)
/-- `vg_hmac_sha512_init`. -/
def initSha512 : Prog isa := scrubF 0 3456 (initCode Spec.Hmac.sha512I sha512Md'.hmacInit sha512F)
/-- `vg_hmac_sha512_224_init`. -/
def initSha512_224 : Prog isa :=
  scrubF 0 3456 (initCode Spec.Hmac.sha512_224I sha512_224Md.hmacInit sha512_224F)
/-- `vg_hmac_sha512_256_init`. -/
def initSha512_256 : Prog isa :=
  scrubF 0 3456 (initCode Spec.Hmac.sha512_256I sha512_256Md.hmacInit sha512_256F)

/-- `vg_hmac_md5_finalize`. -/
def finalizeMd5 : Prog isa := scrubF 0 432 (finCode Spec.Hmac.md5I md5Md)
/-- `vg_hmac_sha1_finalize`. -/
def finalizeSha1 : Prog isa := scrubF 0 496 (finCode Spec.Hmac.sha1I sha1Md)
/-- `vg_hmac_sha224_finalize`. -/
def finalizeSha224 : Prog isa := scrubF 0 880 (finCode Spec.Hmac.sha224I sha224Md)
/-- `vg_hmac_sha256_finalize`. -/
def finalizeSha256 : Prog isa := scrubF 0 880 (finCode Spec.Hmac.sha256I sha256Md)
/-- `vg_hmac_sha384_finalize`. -/
def finalizeSha384 : Prog isa := scrubF 0 1904 (finCode Spec.Hmac.sha384I sha384Md)
/-- `vg_hmac_sha512_finalize`. -/
def finalizeSha512 : Prog isa := scrubF 0 1904 (finCode Spec.Hmac.sha512I sha512Md')
/-- `vg_hmac_sha512_224_finalize`. -/
def finalizeSha512_224 : Prog isa := scrubF 0 1904 (finCode Spec.Hmac.sha512_224I sha512_224Md)
/-- `vg_hmac_sha512_256_finalize`. -/
def finalizeSha512_256 : Prog isa := scrubF 0 1904 (finCode Spec.Hmac.sha512_256I sha512_256Md)

end VG.Impl.Hmac.Stream.Arm.Fn

namespace VG.Impl.Pbkdf2.Whole.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm VG.Impl.Hmac.Stream.Arm

/-- `vg_pbkdf2_hmac_md5`. -/
def md5 : Prog isa := scrubF 0 1088 (pbkdf2Code Spec.Hmac.md5I md5F)
/-- `vg_pbkdf2_hmac_sha1`. -/
def sha1 : Prog isa := scrubF 0 1184 (pbkdf2Code Spec.Hmac.sha1I sha1F)
/-- `vg_pbkdf2_hmac_sha224`. -/
def sha224 : Prog isa := scrubF 0 1664 (pbkdf2Code Spec.Hmac.sha224I sha224F)
/-- `vg_pbkdf2_hmac_sha256`. -/
def sha256 : Prog isa := scrubF 0 1664 (pbkdf2Code Spec.Hmac.sha256I sha256F)
/-- `vg_pbkdf2_hmac_sha384`. -/
def sha384 : Prog isa := scrubF 0 3488 (pbkdf2Code Spec.Hmac.sha384I sha384F)
/-- `vg_pbkdf2_hmac_sha512`. -/
def sha512 : Prog isa := scrubF 0 3488 (pbkdf2Code Spec.Hmac.sha512I sha512F)
/-- `vg_pbkdf2_hmac_sha512_224`. -/
def sha512_224 : Prog isa := scrubF 0 3488 (pbkdf2Code Spec.Hmac.sha512_224I sha512_224F)
/-- `vg_pbkdf2_hmac_sha512_256`. -/
def sha512_256 : Prog isa := scrubF 0 3488 (pbkdf2Code Spec.Hmac.sha512_256I sha512_256F)

end VG.Impl.Pbkdf2.Whole.Arm.Fn
