module

public import VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified
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
public import VerifiedGarbage.Proof.Argon2.Dimensions
public import VerifiedGarbage.Proof.Argon2.IterationsIndices
public import VerifiedGarbage.Proof.Argon2.Permutation
public import VerifiedGarbage.Proof.Argon2.Reference
public import VerifiedGarbage.Proof.Argon2.SegmentIndices
public import VerifiedGarbage.Proof.Argon2.Serialization
public import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords
public import VerifiedGarbage.Proof.Argon2.X86_64.BlockAddress
public import VerifiedGarbage.Proof.Argon2.X86_64.DependentWord
public import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress
public import VerifiedGarbage.Proof.Argon2.X86_64.FillLaneAdvance
public import VerifiedGarbage.Proof.Argon2.X86_64.FillWritePrefix
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
public import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSteps
public import VerifiedGarbage.Proof.Argon2.X86_64.Mix
public import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState
public import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Argon2 on x86-64, for each BLAKE2b backend with the implementation of G for the same CPUs -/

@[expose] public section

namespace VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2

/-- Argon2 for a BLAKE2b backend and an implementation of G of the same
suffix (the baseline with the baseline, `_avx2` with `_avx2`, `_avx512`
with `_avx512`), and BLAKE2b's `_avx2` with G's `_avx512`, for CPUs with
AVX-512F but not AVX512VL (Intel's Knights Landing), which BLAKE2b's
`_avx512` needs: any other pair needs the features of one of these, which
runs both its parts with them. -/
def artifacts (v : Proof.Blake2.X86_64.Backend) (c : Proof.Argon2.X86_64.CompressImpl) :
    List Artifact :=
  have : Proof.Argon2.X86_64.CompressImpl := c
  if !(v.suffix == c.suffix || (v.suffix == "_avx2" && c.suffix == "_avx512")) then [] else
  [Spec.Argon2.deriveApi.artifact VG.X86_64.target {
    suffix := Emit.qualifiedName "" [("blake2b", v.suffix), ("g", c.suffix)]
    code := Impl.Argon2.X86_64.Derive.code ("vg_argon2_hprime" ++ v.suffix)
      (Proof.Argon2.X86_64.HPrime.hash v)
    stack := 344
    verified := Proof.Argon2.X86_64.Derive.verified v _
    spSafe := Proof.Argon2.X86_64.Derive.code_spSafe v _
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2
