module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream

/-!
# HMAC's `init` over the SHA-512 family on x86-64, compressing its two padded keys at once with AVX-512VL

`Proof.Sha512.X86_64.Compress.avx512` is AVX2's compression function with
`vg_sha512_compress2_avx512`, which compresses two blocks at once. Of the
functions made with it only HMAC's `init` runs that one, so only `init` is
an implementation of its own (`init384`, …, in the lists of
`Proof/Variants/MdHash/X86_64.lean`): the others are AVX2's.

`init` is followed by the clearing after each of its two branches
(`MdHash.initAuto`), so it returns without secret residue. It is chosen
only with AVX512_FP16, which its code does not use: it is faster than AVX2's
on Sapphire Rapids and later, and slower on Zen 5, which no feature of its
code tells apart.
-/

@[expose] public section

namespace VG.Proof.Variants.MdHash.X86_64.Sha512Avx512

open Proof.Pbkdf2.Md.X86_64 Proof.Pbkdf2.Md.X86_64.Sha512 VG.X86_64 VG.Impl.Scrub.X86_64

abbrev compress : Proof.Sha512.X86_64.Compress := Proof.Sha512.X86_64.Compress.avx512

/-- The CPU feature `init` is chosen with, beyond those of its code. -/
abbrev extra : List String := ["avx512fp16"]

def init384 : InitImpl Spec.Hmac.sha384I := (sha384 compress).initAuto extra

def init512 : InitImpl Spec.Hmac.sha512I := (sha512 compress).initAuto extra

def init512_224 : InitImpl Spec.Hmac.sha512_224I := (sha512_224 compress).initAuto extra

def init512_256 : InitImpl Spec.Hmac.sha512_256I := (sha512_256 compress).initAuto extra

end VG.Proof.Variants.MdHash.X86_64.Sha512Avx512
