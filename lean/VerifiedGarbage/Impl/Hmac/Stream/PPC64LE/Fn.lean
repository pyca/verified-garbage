module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Impl.Pbkdf2.PPC64LE
public import VerifiedGarbage.Impl.Pbkdf2.Whole.PPC64LE
public import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
public import VerifiedGarbage.Impl.Sha1.PPC64LE.Stream
public import VerifiedGarbage.Impl.Sha256.PPC64LE.Stream
public import VerifiedGarbage.Impl.Sha256.PPC64LE.Md
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Stream
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Md
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Spec.Sha512.Contract

/-!
# HMAC and PBKDF2 on PPC64LE, for each hash function: the functions as emitted

HMAC's code over any streaming hash function (`Impl/Hmac/Stream/PPC64LE.lean`)
and PBKDF2's (`Impl/Pbkdf2/Whole/PPC64LE.lean`), for each hash function with
PPC64LE streaming functions: its streaming functions as that code calls
them (`md5Hash`, `sha1Hash`, …, a `Hash`), HMAC's `init` for a key of any
length (`initCode`), with the frames that hold the working space of `init`
and `finalize` (`hmacFrame`) and of `init` for a long key (`longFrame`), the
functions PBKDF2 calls for it (`fnsOf`: `md5F`, `sha1F`, …), and the frame
that holds PBKDF2's working space (`pbkFrame`).

`Fn` is each function as emitted: its code followed by its cleanup
(`Impl.Scrub.PPC64LE.scrub`), with the result's bits (none), the bytes of
stack its frames use, which the cleanup zeroes, and the volatile registers it
writes, which the cleanup clears (the vector registers SHA-2's compression
functions use), so that it returns without secret residue
(`Proof/Hmac/Stream/PPC64LE/Scrub.lean`, `Proof/Pbkdf2/Whole/PPC64LE/Scrub.lean`).
Each keeps its working space in a frame it does not wipe itself
(`withStackScratch`), and the cleanup zeroes it with the frames below it.
-/

@[expose] public section

namespace VG.Impl.Hmac.Stream.PPC64LE

open VG.PPC64LE

/-! ## The hash functions -/

/-- MD5's streaming functions. -/
def md5Hash : Hash where
  B := 64
  N := 16
  D := 16
  FD := 16
  W := 112
  initN := Spec.Md5.initApi.name
  initC := Impl.Md5.PPC64LE.Stream.init
  updN := "vg_md5_update_scratch"
  updC := Impl.Md5.PPC64LE.Stream.update
  finN := "vg_md5_finalize_scratch"
  finC := Impl.Md5.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_md5_init_scratch"

/-- SHA-1's streaming functions. -/
def sha1Hash : Hash where
  B := 64
  N := 20
  D := 20
  FD := 20
  W := 160
  initN := Spec.Sha1.initApi.name
  initC := Impl.Sha1.PPC64LE.Stream.init
  updN := "vg_sha1_update_scratch"
  updC := Impl.Sha1.PPC64LE.Stream.update
  finN := "vg_sha1_finalize_scratch"
  finC := Impl.Sha1.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_sha1_init_scratch"

/-- SHA-224's streaming functions. -/
def sha224Hash : Hash where
  B := 64
  N := 32
  D := 28
  FD := 32
  W := 160
  initN := Spec.Sha256.init224Api.name
  initC := Impl.Sha256.PPC64LE.Stream.init224
  updN := "vg_sha256_update_scratch"
  updC := Impl.Sha256.PPC64LE.Stream.update
  finN := "vg_sha256_finalize_scratch"
  finC := Impl.Sha256.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_sha224_init_scratch"

/-- SHA-256's streaming functions. -/
def sha256Hash : Hash where
  B := 64
  N := 32
  D := 32
  FD := 32
  W := 160
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.PPC64LE.Stream.init
  updN := "vg_sha256_update_scratch"
  updC := Impl.Sha256.PPC64LE.Stream.update
  finN := "vg_sha256_finalize_scratch"
  finC := Impl.Sha256.PPC64LE.Stream.finalize
  hmacInitN := "vg_hmac_sha256_init_scratch"

/-- The streaming functions of the hash function of the SHA-512 family with
initial hash value `iv` (whose `init` is `initN`) and a digest of `D` bytes,
for HMAC's `init` named `hmacInitN`: its `init`, and SHA-512's `update` and
`finalize`, which writes the whole final hash value (64 bytes), whose first
`D` bytes are the digest. -/
def sha512FamilyHash (iv : Spec.Sha512.HashValue) (D : Nat) (initN hmacInitN : String) : Hash where
  B := 128
  N := 64
  D := D
  FD := 64
  W := 224
  initN := initN
  initC := Impl.Sha512.PPC64LE.Stream.init iv
  updN := "vg_sha512_update_scratch"
  updC := Impl.Sha512.PPC64LE.Stream.update
  finN := "vg_sha512_finalize_scratch"
  finC := Impl.Sha512.PPC64LE.Stream.finalize
  hmacInitN := hmacInitN

/-- SHA-384's streaming functions. -/
def sha384Hash : Hash :=
  sha512FamilyHash Spec.Sha512.H0_384 48 Spec.Sha512.init384Api.name "vg_hmac_sha384_init_scratch"

/-- SHA-512's streaming functions. -/
def sha512Hash : Hash :=
  sha512FamilyHash Spec.Sha512.H0_512 64 Spec.Sha512.init512Api.name "vg_hmac_sha512_init_scratch"

/-- SHA-512/224's streaming functions. -/
def sha512_224Hash : Hash :=
  sha512FamilyHash Spec.Sha512.H0_512_224 28 Spec.Sha512.init512_224Api.name "vg_hmac_sha512_224_init_scratch"

/-- SHA-512/256's streaming functions. -/
def sha512_256Hash : Hash :=
  sha512FamilyHash Spec.Sha512.H0_512_256 32 Spec.Sha512.init512_256Api.name "vg_hmac_sha512_256_init_scratch"

/-! ## HMAC's `init` and the frames -/

/-- The bytes of the frame holding the working space of `init` and
`finalize` (of instance `I`) and its 32-byte header. -/
def hmacFrame (I : Spec.Hmac.Instance) : Nat := 8 * I.scratch + 32

/-- The bytes of the frame holding `initLong`'s working space: 48 bytes fewer
than `hmacFrame`, since `initLong` and the `init` it calls push one frame
more. -/
def longFrame (I : Spec.Hmac.Instance) : Nat := hmacFrame I - 48

/-- `vg_hmac_<hash>_init`, for a key of any length, with `B = 2 ^ b`. -/
def initCode (H : Hash) (I : Spec.Hmac.Instance) (b : Nat) : Prog isa :=
  Hash.initEntry b (Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame I) .r7 H.init)
    (Impl.StackScratch.PPC64LE.withStackScratchWiped (longFrame I) .r7 (H.lbytes / 8) H.initLong)

end VG.Impl.Hmac.Stream.PPC64LE

namespace VG.Impl.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash md5Hash sha1Hash sha224Hash sha256Hash sha384Hash sha512Hash
  sha512_224Hash sha512_256Hash initCode)

/-! ## The functions PBKDF2 calls -/

/-- The functions `pbkdf2` calls for the hash function `H` of instance `I`
(with `B = 2 ^ b`): HMAC's `init` for a key of any length, HMAC's
`finalize` with its working space as an argument, and PBKDF2's `iterate`
(`itC`, with `itW` bytes of working space). -/
def fnsOf (H : Hash) (I : Spec.Hmac.Instance) (b : Nat) (itC : Prog isa) (itW : Nat) : Fns where
  H := H
  Wc := 8 * I.scratch
  hiN := I.initAnyKeyApi.name ++ "_core"
  hiC := initCode H I b
  hfN := s!"vg_hmac_{I.rust}_finalize_scratch"
  itN := s!"vg_pbkdf2_hmac_{I.rust}_iterate"
  itC := itC
  itW := itW

/-- MD5's. -/
def md5F : Fns :=
  fnsOf md5Hash Spec.Hmac.md5I 6
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Md5.PPC64LE.Stream.params 16 "vg_md5_compress" Impl.Md5.PPC64LE.compress)
    (8 * Spec.Hmac.md5I.scratch)

/-- SHA-1's. -/
def sha1F : Fns :=
  fnsOf sha1Hash Spec.Hmac.sha1I 6
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Sha1.PPC64LE.Stream.params 20 "vg_sha1_compress" Impl.Sha1.PPC64LE.compress)
    (8 * Spec.Hmac.sha1I.scratch)

/-- SHA-224's. -/
def sha224F : Fns :=
  fnsOf sha224Hash Spec.Hmac.sha224I 6
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Sha256.PPC64LE.mdParams224 28 "vg_sha256_compress"
      Impl.Sha256.PPC64LE.compress)
    (8 * Spec.Hmac.sha224I.scratch)

/-- SHA-256's. -/
def sha256F : Fns :=
  fnsOf sha256Hash Spec.Hmac.sha256I 6
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Sha256.PPC64LE.mdParams 32 "vg_sha256_compress"
      Impl.Sha256.PPC64LE.compress)
    (8 * Spec.Hmac.sha256I.scratch)

/-- SHA-384's. -/
def sha384F : Fns :=
  fnsOf sha384Hash Spec.Hmac.sha384I 7
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Sha512.PPC64LE.mdParams384 48 "vg_sha512_compress"
      Impl.Sha512.PPC64LE.compress)
    (8 * Spec.Hmac.sha384I.scratch)

/-- SHA-512's. -/
def sha512F : Fns :=
  fnsOf sha512Hash Spec.Hmac.sha512I 7
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Sha512.PPC64LE.mdParams 64 "vg_sha512_compress"
      Impl.Sha512.PPC64LE.compress)
    (8 * Spec.Hmac.sha512I.scratch)

/-- SHA-512/224's. -/
def sha512_224F : Fns :=
  fnsOf sha512_224Hash Spec.Hmac.sha512_224I 7
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Sha512.PPC64LE.mdParams512_224 28 "vg_sha512_compress"
      Impl.Sha512.PPC64LE.compress)
    (8 * Spec.Hmac.sha512_224I.scratch)

/-- SHA-512/256's. -/
def sha512_256F : Fns :=
  fnsOf sha512_256Hash Spec.Hmac.sha512_256I 7
    (Impl.Pbkdf2.PPC64LE.iterate Impl.Sha512.PPC64LE.mdParams512_256 32 "vg_sha512_compress"
      Impl.Sha512.PPC64LE.compress)
    (8 * Spec.Hmac.sha512_256I.scratch)

/-- The bytes of `pbkdf2`'s frame: the working space, above the frame's
32-byte header, rounded up to a multiple of 16. -/
def pbkFrame (I : Spec.Hmac.Instance) : Nat := (8 * I.pbkdf2Scratch + 32 + 15) / 16 * 16

end VG.Impl.Pbkdf2.Whole.PPC64LE

namespace VG.Impl.Hmac.Stream.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)
open VG.Impl.StackScratch.PPC64LE (withStackScratch)

/-- `vg_hmac_md5_init`, as emitted. -/
def initMd5 : Prog isa :=
  scrub 0 512 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (initCode md5Hash Spec.Hmac.md5I 6)

/-- `vg_hmac_md5_finalize`, as emitted. -/
def finalizeMd5 : Prog isa :=
  scrub 0 512 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (withStackScratch (hmacFrame Spec.Hmac.md5I) .r7 md5Hash.finalize)

/-- `vg_hmac_sha1_init`, as emitted. -/
def initSha1 : Prog isa :=
  scrub 0 576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (initCode sha1Hash Spec.Hmac.sha1I 6)

/-- `vg_hmac_sha1_finalize`, as emitted. -/
def finalizeSha1 : Prog isa :=
  scrub 0 576 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (withStackScratch (hmacFrame Spec.Hmac.sha1I) .r7 sha1Hash.finalize)

/-- `vg_hmac_sha224_init`, as emitted. -/
def initSha224 : Prog isa :=
  scrub 0 960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (initCode sha224Hash Spec.Hmac.sha224I 6)

/-- `vg_hmac_sha224_finalize`, as emitted. -/
def finalizeSha224 : Prog isa :=
  scrub 0 960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (hmacFrame Spec.Hmac.sha224I) .r7 sha224Hash.finalize)

/-- `vg_hmac_sha256_init`, as emitted. -/
def initSha256 : Prog isa :=
  scrub 0 960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (initCode sha256Hash Spec.Hmac.sha256I 6)

/-- `vg_hmac_sha256_finalize`, as emitted. -/
def finalizeSha256 : Prog isa :=
  scrub 0 960 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (hmacFrame Spec.Hmac.sha256I) .r7 sha256Hash.finalize)

/-- `vg_hmac_sha384_init`, as emitted. -/
def initSha384 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (initCode sha384Hash Spec.Hmac.sha384I 7)

/-- `vg_hmac_sha384_finalize`, as emitted. -/
def finalizeSha384 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (hmacFrame Spec.Hmac.sha384I) .r7 sha384Hash.finalize)

/-- `vg_hmac_sha512_init`, as emitted. -/
def initSha512 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (initCode sha512Hash Spec.Hmac.sha512I 7)

/-- `vg_hmac_sha512_finalize`, as emitted. -/
def finalizeSha512 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (hmacFrame Spec.Hmac.sha512I) .r7 sha512Hash.finalize)

/-- `vg_hmac_sha512_224_init`, as emitted. -/
def initSha512_224 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (initCode sha512_224Hash Spec.Hmac.sha512_224I 7)

/-- `vg_hmac_sha512_224_finalize`, as emitted. -/
def finalizeSha512_224 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (hmacFrame Spec.Hmac.sha512_224I) .r7 sha512_224Hash.finalize)

/-- `vg_hmac_sha512_256_init`, as emitted. -/
def initSha512_256 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (initCode sha512_256Hash Spec.Hmac.sha512_256I 7)

/-- `vg_hmac_sha512_256_finalize`, as emitted. -/
def finalizeSha512_256 : Prog isa :=
  scrub 0 1952 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (hmacFrame Spec.Hmac.sha512_256I) .r7 sha512_256Hash.finalize)

end VG.Impl.Hmac.Stream.PPC64LE.Fn

namespace VG.Impl.Pbkdf2.Whole.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)
open VG.Impl.StackScratch.PPC64LE (withStackScratch)

/-- `vg_pbkdf2_hmac_md5`, as emitted. -/
def md5 : Prog isa :=
  scrub 0 1616 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (withStackScratch (pbkFrame Spec.Hmac.md5I) .r10 md5F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha1`, as emitted. -/
def sha1 : Prog isa :=
  scrub 0 1776 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (withStackScratch (pbkFrame Spec.Hmac.sha1I) .r10 sha1F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha224`, as emitted. -/
def sha224 : Prog isa :=
  scrub 0 2640 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (pbkFrame Spec.Hmac.sha224I) .r10 sha224F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha256`, as emitted. -/
def sha256 : Prog isa :=
  scrub 0 2640 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (pbkFrame Spec.Hmac.sha256I) .r10 sha256F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha384`, as emitted. -/
def sha384 : Prog isa :=
  scrub 0 5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (pbkFrame Spec.Hmac.sha384I) .r10 sha384F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha512`, as emitted. -/
def sha512 : Prog isa :=
  scrub 0 5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (pbkFrame Spec.Hmac.sha512I) .r10 sha512F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha512_224`, as emitted. -/
def sha512_224 : Prog isa :=
  scrub 0 5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (pbkFrame Spec.Hmac.sha512_224I) .r10 sha512_224F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha512_256`, as emitted. -/
def sha512_256 : Prog isa :=
  scrub 0 5440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]⟩
    (withStackScratch (pbkFrame Spec.Hmac.sha512_256I) .r10 sha512_256F.pbkdf2)

end VG.Impl.Pbkdf2.Whole.PPC64LE.Fn
