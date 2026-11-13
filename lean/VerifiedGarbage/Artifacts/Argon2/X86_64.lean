module

public import VerifiedGarbage.Proof.Argon2.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
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
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
public import VerifiedGarbage.Proof.Variants.Argon2Compress.X86_64
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # Argon2 (RFC 9106) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Argon2.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.Argon2Compress.X86_64.withBlake2b.map
    fun ((v, c) : Proof.Blake2.X86_64.Backend × Proof.Argon2.X86_64.CompressImpl) =>
    have : Proof.Argon2.X86_64.CompressImpl := c
    Spec.Argon2.deriveApi.artifact VG.X86_64.target (VG.X86_64.RScrub.withScrubAllM {
      suffix := qualifiedName "" [("blake2b", v.suffix), ("g", c.suffix)]
      code := Impl.Argon2.X86_64.Derive.code ("vg_argon2_hprime" ++ v.suffix)
        (Proof.Argon2.X86_64.HPrime.hash v)
      stack := 344
      verified := Proof.Argon2.X86_64.Derive.verified v _
      spSafe := Proof.Argon2.X86_64.Derive.code_spSafe v _ }
      (Proof.Argon2.X86_64.Scrub.deriveOut 344))

end VG.Artifacts.Argon2.X86_64
