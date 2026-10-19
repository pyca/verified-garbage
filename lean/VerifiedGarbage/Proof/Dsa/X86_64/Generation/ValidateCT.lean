module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DomainCallCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Validate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateArgs
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
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
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Call2
import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Failure
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Validate
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
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
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
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
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.X86_64.Add
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Call2
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCore
meta import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parity
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReadyReduceCT
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
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
meta import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaOaep.Scan
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Sha256.X86_64.Compress
meta import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
meta import VerifiedGarbage.Spec.Pbkdf2.Generic

/-! # Timing of final parameter validation and its success/retry decision -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.X86_64.Generation

structure ValidatePublic where
  input : ParametersInput
  B : Addr
  F : Addr
  S : Addr
  base : input.base = off B domainCheck
  frame : (⟨F, frameBytes⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩
  hash : (⟨S, oRsa⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩

def ValidatePublic.call (p : ValidatePublic) : DomainCallPublic := ⟨p.input, off p.B packed⟩

def ValidateBefore (pLen qLen : Nat) (p : ValidatePublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ (∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B) ∧
  Scr s p.input.base Impl.Dsa.Layout.usedBytes ∧
  Src s p.input.base Impl.Dsa.Layout.usedBytes (off p.B packed) p.input.params ∧
  p.input.pLen = pLen ∧ p.input.qLen = qLen

theorem validateArgs_ready {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32) (h : ValidateBefore pLen qLen p s) :
    WP isa (.block (validateArgs pLen qLen)) s (DomainCallBefore p.call) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  refine WP.mono (validateArgs_ok L R hp hq) fun t ⟨hd, h8, hdx, hcx, hm, hk⟩ => ?_
  have hd' : t.gpr .rdi = off p.B packed := hb ▸ hd
  refine ⟨⟨hs.congr hk.2.2, (hb ▸ h8).trans p.base.symm,
    by change t.gpr .rdx = BitVec.ofNat 64 p.input.pLen; rw [heP]; exact hdx,
    by change t.gpr .rcx = BitVec.ofNat 64 p.input.qLen; rw [heQ]; exact hcx, ?_⟩, hd'⟩
  rw [hd']
  exact src.congrK (fun _ _ => by rw [hm]) hk

def ValidateResult (p : ValidatePublic) (s : State) : Prop :=
  s.gpr .rsp = p.F ∧ s.gpr .rax = BitVec.ofNat 64
    (if Spec.Dsa.checkParametersBytes p.input.pLen p.input.qLen p.input.params then 1 else 0)

theorem validateCore_result (M : Mont) (Sq : MontS) {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32) (h : ValidateBefore pLen qLen p s) :
    WP isa (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.X86_64.Generate.checkParameters Sq.mm M.mm))
      s (ValidateResult p) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  have step := validateCore_ok M Sq p.input L R (by rw [hb]; exact p.base)
    (by rw [heP]; exact hp) (by rw [heQ]; exact hq) hs (hb ▸ src) p.frame p.hash
  rw [heP, heQ] at step
  exact WP.mono step fun t ⟨hr, Lt, _, _, _⟩ =>
    ⟨Lt.rsp, by simpa only [heP, heQ] using hr⟩

theorem validate_ct_of (M : Mont) (Sq : MontS) (pLen qLen : Nat)
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (validateArgs pLen qLen)) hc).isSome = true) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate Sq.mm M.mm pLen qLen) (fun _ _ => True) := by
  have core : RelCT isa (Two (ValidateBefore pLen qLen))
      (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.X86_64.Generate.checkParameters Sq.mm M.mm))
      (Two ValidateResult) := by
    refine two_post (RelCT.seq (two_piece [.rsp] ?_ ht
      (fun _ _ h => validateArgs_ready hp hq h))
      (two_map ValidatePublic.call (fun _ _ h => h) (domainCall_ct M Sq)))
      (fun _ _ h => validateCore_result M Sq hp hq h)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.rsp.trans ht.1.rsp.symm
  unfold validate
  refine RelCT.seq core (RelCT.seq (two_piece (Ψ := fun (p : ValidatePublic) s => s.gpr .rsp = p.F ∧
    s.zf = some (!(Spec.Dsa.checkParametersBytes p.input.pLen p.input.qLen p.input.params)))
      [.rax] ?_ (by taint_decide) ?_) ?_)
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.trans ht.2.symm
  · intro p s h
    exact WP.mono (validateTest_ok h.2) fun t ⟨hz, _, hk⟩ => ⟨(hk.gpr (by decide)).trans h.1, hz⟩
  · refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    all_goals
      exact two_taint [.rsp] (fun _ _ _ hs ht r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact hs.1.1.trans ht.1.1.symm) (by taint_decide)

theorem validate_ct (M : Mont) (Sq : MontS) (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate Sq.mm M.mm pLen qLen) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact validate_ct_of M Sq _ _ (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
