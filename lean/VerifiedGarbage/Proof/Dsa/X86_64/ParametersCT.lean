module

public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicScheduleCT
public import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
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
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
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
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Call2
import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Failure
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyFailure
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingMain
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingOperands
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Sha256.Stream
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
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
meta import VerifiedGarbage.Proof.Dsa.Derive
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.X86_64.Add
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Call2
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Failure
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.DomainWidths
public import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
public import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
public import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Masks
public import VerifiedGarbage.Proof.Dsa.X86_64.Parity
public import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
public import VerifiedGarbage.Proof.Dsa.X86_64.Save
public import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
public import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
public import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
public import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parity
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
meta import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Result
meta import VerifiedGarbage.Proof.Dsa.X86_64.Save
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyFailure
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingMain
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! # Constant time of the x86-64 DSA domain check

Every input is public: two calls with the same pointers, lengths and domain
bytes take the same path, whatever their scratch holds. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ParametersCall where
  input : ParametersInput
  original : State
  pre : ParametersPre input original

abbrev ParametersCall.layout (c : ParametersCall) : ExecutionLayout :=
  c.input.layout c.original c.pre.pLength c.pre.qLength

structure ParametersAgrees (reference c : ParametersCall) : Prop where
  layout : c.layout = reference.layout
  params : c.input.params = reference.input.params

def ParametersStart (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧ c.original = s

def ParametersEntered (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    KeygenEntryPost c.original c.input.base (checkFieldValues c.original true) s

def ParametersShaped (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    ParametersShapePost c.input c.original c.pre.pLength c.pre.qLength s

def ParametersReady (reference : ParametersCall) (s : State) : Prop :=
  ∃ c : ParametersCall, ParametersAgrees reference c ∧
    ParametersInitialized c.input c.original c.pre.pLength c.pre.qLength s

theorem ParametersAgrees.pLen {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.pLen = reference.input.pLen := congrArg ExecutionLayout.pLen h.layout

theorem ParametersAgrees.qLen {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.qLen = reference.input.qLen := congrArg ExecutionLayout.qLen h.layout

theorem ParametersAgrees.pb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.pb = reference.input.pb := by
  rw [ParametersInput.pb, ParametersInput.pb, h.params, h.pLen]

theorem ParametersAgrees.qb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.qb = reference.input.qb := by
  rw [ParametersInput.qb, ParametersInput.qb, h.params, h.pLen, h.qLen]

theorem ParametersAgrees.gb {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.gb = reference.input.gb := by
  rw [ParametersInput.gb, ParametersInput.gb, h.params, h.pLen, h.qLen]

theorem ParametersAgrees.accepted {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold ParametersInput.accepted
  congr 1
  · exact h.pb
  · exact h.qb

theorem checkEntry_ct : RelCT isa (Two (fun B : Addr => fun s => s.gpr .r8 = B))
    (.block Generate.checkEntry) (fun _ _ => True) :=
  two_taint [.r8] (pins_of (fun B _ => B) (by
    intro B s h r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h)) (by taint_decide)

theorem parametersEntered_ct : RelCT isa (Two ParametersStart) (.block Generate.checkEntry)
    (Two ParametersEntered) := by
  refine two_post (two_map (fun c : ParametersCall => c.layout.base) ?_ checkEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact c.pre.base.trans (congrArg ExecutionLayout.base ha.layout)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (checkEntry_ok c.pre.scratch c.pre.base) fun t ht => ⟨c, ha, ht⟩

def ParametersCall.shape (c : ParametersCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.pb
  qBytes := c.input.qb
  digestLen := 0
  extentBound := by decide
  pPositive := c.input.pPositive
  qPositive := c.input.qPositive
  pBound := by rw [c.input.pbLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega
  qBound := by rw [c.input.qbLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega
  digestBound := by decide

theorem ParametersAgrees.shape {reference c : ParametersCall} (h : ParametersAgrees reference c) :
    c.shape = reference.shape := by
  unfold ParametersCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pb
  · exact h.qb

theorem ParametersEntered.context {reference : ParametersCall} {s : State} (h : ParametersEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hf (he.keep.mono (by decide))
  refine ⟨c.pre.scratch.congr he.keep.2.2, he.base, he.fields .p (by decide) (by decide),
    he.fields .q (by decide) (by decide), ?_, ?_, he.fields .digestLen (by decide) (by decide), hps, hqs⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.pb.length
    rw [c.input.pbLength]
    exact (he.fields .pLen (by decide) (by decide)).trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.qb.length
    rw [c.input.qbLength]
    exact (he.fields .qLen (by decide) (by decide)).trans c.pre.qLength

theorem parametersShape_ct : RelCT isa (Two ParametersStart)
    (.seq (.block Generate.checkEntry) Checks.domainShape) (Two ParametersShaped) := by
  refine two_post (RelCT.seq parametersEntered_ct
    (two_map ParametersCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (parametersShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

theorem ParametersShaped.branch {reference : ParametersCall} {s : State} (h : ParametersShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

theorem ParametersShaped.rdi {reference : ParametersCall} {s : State} (h : ParametersShaped reference s) :
    s.gpr .rdi = reference.layout.base := by
  obtain ⟨c, ha, hs⟩ := h
  exact hs.rdi.trans (congrArg ExecutionLayout.base ha.layout)

def ParametersCall.initialization (c : ParametersCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.pb
  qBytes := c.input.qb
  pLength := c.input.pbLength
  qLength := c.input.qbLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem ParametersShaped.initialization {reference : ParametersCall} {s : State}
    (h : ParametersShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  obtain ⟨hps, hqs, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.pb := hps
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.qb := hqs
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedParametersCall := {c : ParametersCall // c.input.accepted = true}

theorem parametersWorkspaces_ct : RelCT isa (Two (fun c : AcceptedParametersCall => ParametersShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedParametersCall => ParametersReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedParametersCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (parametersInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

/-- The domain's operands, as the schedule reads them. -/
def parametersInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen)]

theorem parametersInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ parametersInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [parametersInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]

def ParametersCall.schedule (c : ParametersCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.pb
    rw [c.input.pbLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.qb
    rw [c.input.qbLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

theorem ParametersReady.body {reference : ParametersCall} {s : State} (ha : reference.input.accepted = true)
    (h : ParametersReady reference s) : ∃ pi qi, PublicKeyPre parametersInputs (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, _⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change ParametersOperands (c.layout.withInverses pi qi) c.input s at ho
  rw [hag.layout] at hr ho hmask
  have hgl : c.input.gb.length = reference.layout.pLen := c.input.gbLength.trans hag.pLen
  have hql : c.input.qb.length = reference.layout.qLen := c.input.qbLength.trans hag.qLen
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, c.input.qb, ho.subgroup, hql, ?_⟩
  · intro a ha
    simp only [parametersInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨_, ho.publicValue, hgl⟩
    · exact ⟨_, ho.subgroup, hql⟩
    · exact ⟨_, ho.generator, hgl⟩
  · change Spec.Dsa.decodeBE c.input.qb = Spec.Dsa.decodeBE reference.input.qb
    rw [hag.qb]

theorem parametersReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedParametersCall => ParametersReady c.val) s₁ s₂) :
    Two (PublicKeyPre parametersInputs) s₁ s₂ := by
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem parametersBody_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (PublicKeyPre parametersInputs))
    (seqs [Checks.signingKey Sq.mm M.mm, .block SignVerify.result]) (fun _ _ => True) := by
  have h1 := signingKey_ct M Sq parametersInputs (fun p => parametersInputs_stable p)
    (by intro p; simp [parametersInputs]) (by intro p; simp [parametersInputs])
    (by intro p; simp [parametersInputs])
  unfold seqs
  refine RelCT.seq h1 ?_
  exact two_map (fun p => p.layout.base) (fun _ _ h => h.1.parent.rdi) result_ct

theorem parametersSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedParametersCall => ParametersShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq parametersWorkspaces_ct ?_
  exact (parametersBody_ct M Sq).mono (fun _ _ h => parametersReady_related h) (fun _ _ h => h)

theorem parametersMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two ParametersStart) (Generate.checkParameters Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq parametersShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map (fun c : ParametersCall => c.layout.base) (fun _ _ h => h.rdi) verifyFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (parametersSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64
