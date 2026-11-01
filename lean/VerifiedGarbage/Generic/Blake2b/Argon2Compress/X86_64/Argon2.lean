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
public import VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified
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

/-! # Argon2 on x86-64, for every BLAKE2b backend and every implementation of G -/

@[expose] public section

namespace VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2

def artifacts (v : Proof.Blake2.X86_64.Backend) (c : Proof.Argon2.X86_64.CompressImpl) :
    List Artifact :=
  have : Proof.Argon2.X86_64.CompressImpl := c
  [Spec.Argon2.deriveApi.artifact VG.X86_64.target {
    suffix := Emit.qualifiedName "" [("blake2b", v.suffix), ("g", c.suffix)]
    code := Impl.Argon2.X86_64.Derive.code ("vg_argon2_hprime" ++ v.suffix)
      (Proof.Argon2.X86_64.HPrime.hash v)
    stack := 344
    verified := Proof.Argon2.X86_64.Derive.verified v _
    spSafe := Proof.Argon2.X86_64.Derive.code_spSafe v _
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.Blake2b.Argon2Compress.X86_64.Argon2
