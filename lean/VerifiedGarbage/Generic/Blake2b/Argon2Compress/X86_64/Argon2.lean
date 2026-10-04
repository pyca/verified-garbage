import VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified

/-!
# Argon2 on x86-64, for every BLAKE2b backend and every implementation of G

A generic file of two interfaces (see `TCB/Emit.lean`): `vg_argon2` calls
both the BLAKE2b streaming functions of a backend `v`
(`Variants/Blake2b/X86_64/`), through H₀ and `vg_argon2_hprime`, and an
implementation `c` of the compression function G
(`Variants/Argon2Compress/X86_64/`), and is emitted once for each pair,
named with both suffixes (e.g. `vg_argon2_avx2` for G with AVX2), needing
both's CPU features.
-/

namespace VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2

def artifacts (v : Proof.Blake2.X86_64.Backend) (c : Proof.Argon2.X86_64.CompressImpl) :
    List Artifact :=
  have : Proof.Argon2.X86_64.CompressImpl := c
  [{ Spec.Argon2.deriveApi with
    name := Spec.Argon2.deriveApi.name ++ v.suffix ++ c.suffix
    target := VG.X86_64.target
    doc := Spec.Argon2.deriveApi.doc
      (notes := ["Serial lane evaluation honors every positive worker limit. All hashing uses \
        the selected BLAKE2b streaming backend, including H₀ and every H′ call, and every \
        compression calls `" ++ Spec.Argon2.compressApi.name ++ c.suffix ++ "`."])
    code := Impl.Argon2.X86_64.Derive.code (Spec.Argon2.hPrimeApi.name ++ v.suffix)
      (Proof.Argon2.X86_64.HPrime.hash v)
    contract := Spec.Argon2.deriveContract VG.X86_64.abi 344
    stack := 344
    verified := Proof.Argon2.X86_64.Derive.verified v _
    spSafe := Proof.Argon2.X86_64.Derive.code_spSafe v _
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2
