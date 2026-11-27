module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveScrub
import VerifiedGarbage.Impl.Argon2.X86_64.Fn
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveLit
import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit
import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit
import VerifiedGarbage.Proof.Argon2.X86_64.ParametersLit
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupCT
import VerifiedGarbage.Proof.Blake2.X86_64.Lit
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.IterationsIndices
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.SegmentIndices
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords
import VerifiedGarbage.Proof.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Proof.Argon2.X86_64.DependentWord
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompress
import VerifiedGarbage.Proof.Argon2.X86_64.FillLaneAdvance
import VerifiedGarbage.Proof.Argon2.X86_64.FillWritePrefix
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSteps
import VerifiedGarbage.Proof.Argon2.X86_64.Mix
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Argon2 (RFC 9106) on x86-64 -/

namespace VG.Artifacts.Argon2.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.Argon2Compress.X86_64.withBlake2b.map
    fun ((v, c) : Proof.Blake2.X86_64.Backend × Proof.Argon2.X86_64.CompressImpl) =>
    letI : Proof.Argon2.X86_64.CompressImpl := c
    Spec.Argon2.deriveApi.artifact VG.X86_64.target {
      suffix := qualifiedName "" [("blake2b", v.suffix), ("g", c.suffix)]
      code := Impl.Argon2.X86_64.Fn.derive (v.level.join c.level) ("vg_argon2_hprime" ++ v.suffix)
        (Proof.Argon2.X86_64.HPrime.hash v)
      verified := Proof.Argon2.X86_64.Derive.derive_scrubbed v _
      spSafe := Proof.Argon2.X86_64.Derive.derive_spSafe v _ _ }

spec_apis artifacts

end VG.Artifacts.Argon2.X86_64
