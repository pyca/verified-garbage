module

import VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified
public import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Argon2.X86_64.DeriveLit
public import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT
public import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit
public import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
public import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
public import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit
public import VerifiedGarbage.Proof.Argon2.X86_64.ParametersLit
public import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
public import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupCT
public import VerifiedGarbage.Proof.Blake2.X86_64.Lit

/-!
# Argon2 on x86-64, for every BLAKE2b backend and every implementation of G

A generic file of two interfaces (see `TCB/Emit.lean`): `vg_argon2` calls
both the BLAKE2b streaming functions of a backend `v`
(`Variants/Blake2b/X86_64/`), through H₀ and `vg_argon2_hprime`, and an
implementation `c` of the compression function G
(`Variants/Argon2Compress/X86_64/`), and is emitted once for each pair,
named by `Emit.qualifiedName` with the tags `blake2b` and `g` (e.g.
`vg_argon2_g_avx2` for G with AVX2 and BLAKE2b's baseline backend),
needing both's CPU features.
-/

@[expose] public section

namespace VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2

def artifacts (v : Proof.Blake2.X86_64.Backend) (c : Proof.Argon2.X86_64.CompressImpl) :
    List Artifact :=
  have : Proof.Argon2.X86_64.CompressImpl := c
  [Spec.Argon2.deriveApi.artifact VG.X86_64.target {
    suffix := Emit.qualifiedName "" [("blake2b", v.suffix), ("g", c.suffix)]
    notes := ["Serial lane evaluation honors every positive worker limit. All hashing uses \
        the selected BLAKE2b streaming backend, including H₀ and every H′ call, and every \
        compression calls `" ++ Spec.Argon2.compressApi.name ++ c.suffix ++ "`."]
    code := Impl.Argon2.X86_64.Derive.code (Spec.Argon2.hPrimeApi.name ++ v.suffix)
      (Proof.Argon2.X86_64.HPrime.hash v)
    stack := 344
    verified := Proof.Argon2.X86_64.Derive.verified v _
    spSafe := Proof.Argon2.X86_64.Derive.code_spSafe v _
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2
