module

import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.PrivateKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PrivateKeyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.CoreSignCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CoreSignCT
public import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerifyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerifyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SignCompute
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignCompute
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyCompute
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyCompute
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Dsa.X86_64.Call2
import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepareCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Minus
import VerifiedGarbage.Proof.Dsa.X86_64.MinusStep
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.Workspaces
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.X86_64.Add
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Call2
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByteCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepareCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Minus
meta import VerifiedGarbage.Proof.Dsa.X86_64.MinusStep
meta import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
meta import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.X86_64.Workspaces
meta import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Constant time of validation and signing/verification together -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def signComputeInputs (p : SchedulePublic) : List (Operand × Nat) :=
  (Core.publicValue, p.layout.pLen) :: (⟨.input .q, .qLen⟩, p.layout.qLen) :: signInputs p

def verifyComputeInputs (p : SchedulePublic) : List (Operand × Nat) :=
  (⟨.input .q, .qLen⟩, p.layout.qLen) :: verifyInputs p

theorem signComputeInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ signComputeInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [signComputeInputs, List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · exact signInputs_stable p a ha

theorem verifyComputeInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ verifyComputeInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [verifyComputeInputs, List.mem_cons] at ha
  rcases ha with rfl | ha
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · exact verifyInputs_stable p a ha

theorem signCompute_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (PublicKeyPre signComputeInputs))
    (signCompute Sq.mm M.mm) (Two (ScheduleState signComputeInputs)) := by
  have h1 := signingKey_ct M Sq signComputeInputs signComputeInputs_stable
    (by intro p; simp [signComputeInputs, signInputs])
    (by intro p; simp [signComputeInputs]) (by intro p; simp [signComputeInputs])
  have h2 := privateKey_ct M Sq signComputeInputs signComputeInputs_stable
    (by intro p; simp [signComputeInputs, signInputs]) (by intro p; simp [signComputeInputs])
    (by intro p; simp [signComputeInputs, signInputs]) (by intro p; simp [signComputeInputs, signInputs])
  have h3 := coreSignSchedule_ct M Sq signComputeInputs signComputeInputs_stable
    (by intro p a ha; simp [signComputeInputs, ha])
  have h4 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar r)
    (fun p => p.layout.qLen) true (by change r < 2 ^ 31; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  have h5 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar s)
    (fun p => p.layout.qLen) true (by change s < 2 ^ 31; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  unfold signCompute seqs
  refine RelCT.seq h1 (RelCT.seq h2 (RelCT.seq h3 (RelCT.seq (R := Two (ScheduleState signComputeInputs)) ?_ ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q r (by decide) (scalar_space (by decide) p)⟩) h4
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q s (by decide) (scalar_space (by decide) p)⟩) h5

theorem verifyCompute_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (PublicKeyPre verifyComputeInputs))
    (verifyCompute Sq.mm M.mm) (Two (ScheduleState verifyComputeInputs)) := by
  have h1 := publicKey_ct M Sq verifyComputeInputs verifyComputeInputs_stable
    (by intro p; simp [verifyComputeInputs, verifyInputs])
    (by intro p; simp [verifyComputeInputs, verifyInputs]) (by intro p; simp [verifyComputeInputs])
  have h2 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureR
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.signatureR])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := scheduleRange_ct verifyComputeInputs verifyComputeInputs_stable .q Core.signatureS
    (fun p => p.layout.qLen) false (by trivial) (by trivial)
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h4 := coreVerifySchedule_ct M Sq verifyComputeInputs verifyComputeInputs_stable
    (by intro p a ha; simp [verifyComputeInputs, ha])
  have h5 := scheduleEqual_ct verifyComputeInputs verifyComputeInputs_stable (Core.scalar u) Core.signatureR
    (fun p => p.layout.qLen) false (by change u < 2 ^ 31; decide) (by trivial) (by trivial)
    (by simp [stablePointer, Core.signatureR]) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega) (by taint_decide)
  unfold verifyCompute seqs
  refine RelCT.seq h1 (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_
    (RelCT.seq (R := Two (ScheduleState verifyComputeInputs)) ?_ (RelCT.seq h4 ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h2
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.signatureS, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h3
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q u (by decide) (scalar_space (by decide) p),
        (h.2.1 (Core.signatureR, p.layout.qLen) (by simp [verifyComputeInputs, verifyInputs])).active⟩) h5

end VG.Proof.Dsa.X86_64
