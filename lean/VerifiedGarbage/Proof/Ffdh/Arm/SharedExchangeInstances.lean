module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPower
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMainCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPowerCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainNormalizedPrepareAtCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedCheckPublic
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAtCT
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.HeadCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.Arm.Target
public import Init.Core
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangePre
import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PowerAt
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.Arm.SharedExchangeVerified`, which only this module used -/

section

/-! ### `Ffdh.Arm.SharedExchangeCorrect`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SharedExchangePre`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SharedExchangeFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.SharedExchangeMain`, which only this module used -/

section

/-! Native shared-secret exponentiation, range checking, export, and rejection masking. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

theorem main_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P)
    (peer : Octets p.base p.publicValue p.len yb s) (peerLength : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (scalarFit : xb.length < 2 ^ 32)
    (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t =>
      t.gpr .r0 = (if sharedAccepted p yb xb then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.output) p.k =
        (if sharedAccepted p yb xb then Spec.Rsa.i2osp (sharedValue p yb xb) p.k else List.replicate p.k 0) ∧
      Frame (writes p s) s.mem t.mem := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have extend {m m' : Mem} (f : Frame [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48] m m') : Frame (writes p s) m m' :=
    f.mono (by simp [writes, exchangeWrites])
  rw [VG.Impl.Ffdh.Arm.SharedExchange.main, WP.seq_iff]
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h calls.toDomainCallMemory stable h0 h24 h32 large odd normalized) ?_
  rintro u ⟨contextU, readyU, modU, r2U, frameU, restU⟩
  have prepareSeparate {src : BitVec 32} {bs : List Byte}
      (octets : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (ifBelow : Region.Disjoint ⟨State.addr src, bs.length⟩ (FrameStack.belowA s.sp 48))
      (r : Region) (hr : r ∈ domainPrepareWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact octets.separate
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact ifBelow
  have peerU := peer.after_frame frameU restU (prepareSeparate peer peerStack (by rw [peerLength]; exact calls.publicValue))
  have scalarU := scalar.after_frame frameU restU (prepareSeparate scalar scalarStack calls.scalarBelow)
  rw [WP.seq_iff]
  refine WP.mono (sharedCheckPublicPower_ok backend u 36 40 44 contextU (calls.after restU).toDomainCallMemory stable h36 h40 h44 h32 readyU modU odd r2U
    peerU peerLength scalarU positive scalarFit scalarCount (by rw [restU.sp]; exact calls.scalarBelow)) ?_
  rintro v ⟨contextV, readyV, power, modV, _, _, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok v readyV op6 (by decide) (by rw [modV]; exact odd)) ?_
  rintro w ⟨readyW, flag, arraysW, frameW, restW⟩
  have contextW := contextV.after_workspace frameW restW readyW.ptr (fun d hd => (stableSlots_at stable hd).1)
  have valueW := (arraysW 6 op6 (by decide)).trans power
  have flagW : w.gpr .r11 = if sharedAccepted p yb xb then 1 else 0 := by
    rw [power, modV] at flag
    change w.gpr .r11 = if decide (1 < sharedValue p yb xb ∧ sharedValue p yb xb < p.P - 1) = true then 1 else 0
    change w.gpr .r11 = (if 1 < sharedValue p yb xb ∧ sharedValue p yb xb < p.P - 1 then 1 else 0) at flag
    simpa only [decide_eq_true_eq] using flag
  have valueFit : numAt w.mem (State.addr p.base) p.w 6 < 2 ^ (8 * p.k) := by
    rw [valueW, VG.Proof.Bignum.powMod_eq]
    exact Nat.lt_trans (Nat.mod_lt _ (by omega_using [large] : 0 < p.P)) p.modulusBound
  change WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.saveResult)
    (.seq VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult VG.Impl.Ffdh.Arm.Domain.Exchange.maskOutput)) w _
  refine WP.mono (exchangeFinish_ok w (sharedAccepted p yb xb) contextW stable h4 h32 saved readyW
    (((output.after restU).after restV).after restW) workspaceSep
    (by rw [restW.sp, restV.sp, restU.sp]; exact stackSep) valueFit flagW) ?_
  rintro t ⟨status, bytes, frameT, _⟩
  rw [valueW] at bytes
  refine ⟨status, bytes, ?_⟩
  have fU : Frame (writes p s) s.mem u.mem := frameU.sub (by
    intro r hr
    simp only [domainPrepareWrites, prepareAtWrites, prepareWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact ⟨⟨State.addr p.base, 8 * p.len⟩, by simp [writes, exchangeWrites], by intro a ha; exact ha⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [writes, exchangeWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨FrameStack.belowA s.sp 48, by simp [writes], by intro a ha; exact ha⟩)
  have fT : Frame (writes p s) w.mem t.mem := by
    have localFrame := frameT.mono (by simp [writes, exchangeWrites] : ∀ r ∈ exchangeWrites p w, r ∈ writes p w)
    simpa only [writes, exchangeWrites, restW.sp, restV.sp, restU.sp] using localFrame

  have fV : Frame (writes p s) u.mem v.mem := by
    apply extend
    simpa only [restU.sp] using frameV
  have fW : Frame (writes p s) v.mem w.mem := frameW.mono (by simp [writes, exchangeWrites])
  exact ((fU.trans fV).trans fW).trans fT

end VG.Proof.Ffdh.Arm.SharedExchange

end

end

/-! AAPCS shared-secret computation with native validation and output handling. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedExchangeBody.lean`, which only this module imported.
section

/-! The shared-value body is safe for all domain encodings, and specified for valid moduli. -/

section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem body_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : Context p slots s) (calls : CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (peer : Octets p.base p.publicValue p.len yb s) (peerLength : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (scalarFit : xb.length < 2 ^ 32)
    (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → exchangeResult p yb xb t) ∧
      Frame (writes p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨context, zero, frame, rest⟩
  have entryFrame : Frame (writes p s) s.mem u.mem := frame.mono (by simp [writes, exchangeWrites])
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    have facts := VG.Proof.Bignum.valid_facts valid p.minLength
    have stable' : stableSlots (60 :: 56 :: slots) = true := by
      change (true && (true && stableSlots slots)) = true
      rw [Bool.true_and, Bool.true_and, stable]
    have sourceFrame {src : BitVec 32} {bs : List Byte}
        (separate : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact separate
    have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | rfl | hd
      · exact Or.inl (by decide)
      · exact Or.inl (by decide)
      · exact saved d hd
    refine WP.mono (main_ok backend u context (calls.after rest) stable' (by simp [h0]) (by simp [h4]) (by simp [h24])
      (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) saved' facts.2.1 facts.1 facts.2.2
      (peer.after_frame frame rest (sourceFrame peerStack)) peerLength
      (scalar.after_frame frame rest (sourceFrame scalarStack)) positive scalarFit scalarCount
      (by rw [rest.sp]; exact peerStack) (by rw [rest.sp]; exact scalarStack) (output.after rest)
      workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
    rintro t ⟨result, bytes, frameT⟩
    exact ⟨fun _ => ⟨result, bytes⟩, entryFrame.trans (by simpa only [writes, exchangeWrites, rest.sp] using frameT)⟩
  · have invalid : Spec.Rsa.modulusValid p.P p.k = false := Bool.eq_false_iff.mpr valid
    refine WP.ite false (by change some u.z = some false; rw [zero, invalid]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨_, mem⟩, _⟩
    exact ⟨fun hv => (valid hv).elim, by rw [mem]; exact entryFrame⟩

end VG.Proof.Ffdh.Arm.SharedExchange
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem entered_ok (backend : MontBackend) (s : State) {p : Inputs} {yb xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : ExchangeIncoming p s) (calls : CallMemory p xb.length s)
    (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length)
    (peer : Octets p.base p.publicValue p.len yb s) (peerLength : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length) (scalarFit : xb.length < 2 ^ 32)
    (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))) s fun t =>
        (Spec.Rsa.modulusValid p.P p.k = true → exchangeResult p yb xb t) ∧
        Frame (writes p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (exchangeEntry_ok s h incoming out domain domainLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte}
      (separate : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    rw [List.mem_singleton] at hr; subst r; exact separate
  refine WP.mono (body_ok backend u context (calls.after rest) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    (peer.after_frame frame rest (sourceSep peerStack)) peerLength
    (scalar.after_frame frame rest (sourceSep scalarStack)) positive scalarFit scalarCount
    (by rw [rest.sp]; exact peerStack) (by rw [rest.sp]; exact scalarStack) (output.after rest)
    workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (writes p s) s.mem u.mem := frame.mono (by simp [writes, exchangeWrites])
  exact ⟨result, entryFrame.trans (by simpa only [writes, exchangeWrites, rest.sp] using frameT)⟩

structure FnInput (p : Inputs) (yb xb : List Byte) (s : State) : Prop where
  input : ExchangeFnInput p yb xb s
  calls : CallMemory p xb.length (entered s)
  saved : ∀ r ∈ writes p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem fn_ok (backend : MontBackend) (s : State) {p : Inputs} {yb xb : List Byte} (h : FnInput p yb xb s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedExchange.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s fun t => abiPreserved s t ∧
      (Spec.Rsa.modulusValid p.P p.k = true → exchangeResult p yb xb t) := by
  unfold VG.Impl.Ffdh.Arm.SharedExchange.code
  refine framed_of_separate _ s h.input.stackFits (writes p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true → status = (if sharedAccepted p yb xb then 1 else 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.output) p.k =
        (if sharedAccepted p yb xb then Spec.Rsa.i2osp (sharedValue p yb xb) p.k else List.replicate p.k 0)) h.saved ?_
    (hQ := fun m₁ m₂ v hf hq hv => by
      obtain ⟨st, bytes⟩ := hq hv
      refine ⟨st, Eq.trans (VG.Proof.Rsa.rsa_bytes_frame hf (by have := h.input.output.fits; omega_using [this])
        fun r hr => ?_) bytes⟩
      simp only [released, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.saved _ (by simp [writes, exchangeWrites])).symm
      · exact h.input.stackSep.symm)
  refine WP.mono (entered_ok backend (entered s) h.input.args h.input.incoming h.calls h.input.out h.input.domain h.input.domainLength
    h.input.peer h.input.peerLength h.input.scalar h.input.positive h.input.scalarFit h.input.scalarCount h.input.peerStack h.input.scalarStack h.input.output
    h.input.workspaceSep h.input.stackSep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm.SharedExchange

end

end

/-! Exchange reserves the outer frame plus the callable arithmetic stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem pre128 (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s) :
    (Spec.Ffdh.exchangeContract abi 128).pre s := by
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre ⊢
  obtain ⟨stackFit, argFit, rd, wr, outDom, outX, outY, outS, outArgs, domS, xS, yS, sArgs,
    stackOut, stackDom, stackX, stackY, stackS, stackArgs, outFit, domFit, xFit, yFit, sFit,
    bounds, domainLen, outLen, yLen, xPositive, xMax, space⟩ := pre
  have inner : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 128, 128⟩
      ⟨State.addr s.sp - BitVec.ofNat 64 176, 176⟩ :=
    Offset.below_mono _ (by decide) (by decide)
  exact ⟨by omega_using [stackFit], argFit, rd, wr, outDom, outX, outY, outS, outArgs, domS, xS, yS, sArgs,
    stackOut.sub_left inner, stackDom.sub_left inner, stackX.sub_left inner,
    stackY.sub_left inner, stackS.sub_left inner, stackArgs.sub_left inner,
    outFit, domFit, xFit, yFit, sFit, bounds, domainLen, outLen, yLen, xPositive, xMax, space⟩

theorem input (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s)
    {p : Inputs} {yb xb : List Byte}
    (base : stackArg s 5 = p.base) (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (peer : stackArg s 3 = p.publicValue) (scalar : stackArg s 1 = p.privateValue)
    (count : (stackArg s 0).toNat = p.k) (capacity : (stackArg s 6).toNat = p.len)
    (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom)
    (peerBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    FnInput p yb xb s := by
  have old := exchange_input s (pre128 s pre) base out domain peer scalar count capacity privateCount domainBytes peerBytes scalarBytes
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, _, _, _, _, _, _, _, _, _, _, _, stackOut, stackDom, stackX, stackY, stackS,
    _, _, _, _, _, _, _, _, outLen, yLen, _, _, _⟩ := pre
  have domLen : (s.gpr .r3).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have xLen : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [outLen,count,out] at stackOut
  rw [yLen,count,peer] at stackY
  rw [privateCount,scalar] at stackX
  rw [domain,domLen] at stackDom
  rw [base,capacity,Nat.mul_comm p.len 8] at stackS
  have reserved : State.addr s.sp - BitVec.ofNat 64 176 = State.addr (s.sp - BitVec.ofNat 32 176) :=
    (addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackOut stackDom stackX stackY stackS
  have calls := CallMemory.of_outer (p := p) (n := xb.length) stackFit (entered_sp s)
    stackS stackDom.symm stackY.symm (by rw [xLen]; exact stackX.symm) stackOut.symm
  refine ⟨old,calls,?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact old.saved r hr
  · have eq := List.mem_singleton.mp hr
    subst r
    have shifted : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
    have fit : (entered s).sp.toNat + 72 < 2^32 := by
      rw [entered_nat s (by omega_using [stackFit])]; have := s.sp.isLt; omega_using []
    rw [shifted,VG.Arm.addr_add fit,belowA,addr_sub' calls.stack.fit]
    exact (Offset.disjoint_below_above _ (m:=48) (a:=72) (l:=56) (by decide)).symm

end VG.Proof.Ffdh.Arm.SharedExchange

end

end

/-! ### `Ffdh.Arm.SharedExchangePrograms`, which this module and modules that import it used -/

section

/-! One shared-secret exponentiation program for every shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedExchange.code (MontCall.op b.name b.mul)

end VG.Proof.Ffdh.Arm.SharedExchange

end

end

/-! The callable shared-secret computation satisfies the architecture-independent contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem data (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s) :
    ∃ (p : Inputs) (yb xb : List Byte), stackArg s 5 = p.base ∧ s.gpr .r0 = p.output ∧
      s.gpr .r2 = p.domain ∧ stackArg s 3 = p.publicValue ∧ stackArg s 1 = p.privateValue ∧
      (stackArg s 0).toNat = p.k ∧ (stackArg s 6).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ FnInput p yb xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  have domLength : dom.length = (s.gpr .r3).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 5
    domain := s.gpr .r2
    publicValue := stackArg s 3
    privateValue := stackArg s 1
    output := s.gpr .r0
    entropy := 0
    len := (stackArg s 6).toNat
    k := (stackArg s 0).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((s.gpr .r3).toNat = 3 * (stackArg s 0).toNat)
    dom := dom
    minLength := bounds.1
    maxLength := bounds.2
    space := space
    domainLength := by
      rw [domLength]
      simp only [decide_eq_true_eq]
      split
      · assumption
      · rename_i different
        rcases domainLen with h | h
        · exact h
        · exact False.elim (different h) }
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 0).toNat
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, yb, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    input s original (p := p) (yb := yb) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem correct (backend : MontBackend) (s : State) (pre : (Spec.Ffdh.exchangeContract abi 176).pre s) :
    ∃ tr t, Exec isa (code backend) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.exchangeContract abi 176).post s t := by
  obtain ⟨p, yb, xb, _, out, domain, peer, scalar, count, _, privateCount,
    domainBytes, peerBytes, scalarBytes, input⟩ := data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := fn_ok backend s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have lengths : (s.gpr .r1).toNat = (stackArg s 0).toNat ∧
      (stackArg s 4).toNat = (stackArg s 0).toNat := by
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, outLen, yLen, _, _, _⟩ := pre
    exact ⟨outLen, yLen⟩
  sig_post [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes peerBytes scalarBytes
  simp only [lengths.1, lengths.2, count, domain, peer, scalar, privateCount, domainBytes,
    peerBytes, scalarBytes, out]
  intro valid validPeer
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  exact exchangeResult_spec valid validPeer (result modValid)

end VG.Proof.Ffdh.Arm.SharedExchange

end

end

/-! ### `Ffdh.Arm.SharedExchangeContractCT`, which only this module used -/

section

/-! The shared exchange timing policy is satisfied even when private values and statuses differ. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedExchangeMainCT.lean`, which only this module imported.
section

/-! Callable exchange preserves the private scalar's fixed public-length trace. -/

section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

structure MainInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    ExchangeMainInput p slots yb xb s where
  calls : CallMemory p xb.length s

structure PowerInput (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop extends
    ExchangePowerInput p slots yb xb s where
  calls : CallMemory p xb.length s

theorem prepare_power (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : MainInput p slots yb xb s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (peerLength : yb.length = p.k) (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 24) s (PowerInput p slots yb xb) := by
  refine WP.mono (domainNormalizedPrepareAt24_ok backend s h.context h.calls.toDomainCallMemory stable h0 h24 h32 large odd normalized) ?_
  rintro u ⟨context, ready, modulus, r2, frame, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte} (source : Octets p.base src p.len bs s)
      (stack : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (below : Region.Disjoint ⟨State.addr src, bs.length⟩ (FrameStack.belowA s.sp 48))
      (r : Region) (hr : r ∈ domainPrepareWrites p s) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    simp only [domainPrepareWrites, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact source.separate
      · exact stack.sub_right (Offset.sub_base _ (by decide))
      · exact stack.sub_right (Offset.sub_base _ (by decide))
    · exact below
  exact ⟨⟨⟨context, ready, modulus, r2,
    h.peer.after_frame frame rest (sourceSep h.peer h.peerStack (by rw [peerLength]; exact h.calls.publicValue)),
    h.scalar.after_frame frame rest (sourceSep h.scalar h.scalarStack h.calls.scalarBelow)⟩,
    h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩, h.calls.after rest⟩

theorem power_finish (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {yb xb : List Byte}
    (h : PowerInput p slots yb xb s) (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb.length) (fits : xb.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb.length) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36 40 44) s (ExchangePowered p slots) := by
  refine WP.mono (sharedCheckPublicPower_ok backend s 36 40 44 h.context h.calls.toDomainCallMemory stable
    h36 h40 h44 h32 h.ready h.modulus odd h.r2 h.source peerLength h.exponent positive fits count h.calls.scalarBelow) ?_
  rintro u ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.output.after rest, h.workspaceSep, by rw [rest.sp]; exact h.stackSep, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  exact Nat.lt_trans (Nat.mod_lt _ (by have := h.ready.modulus; rw [h.modulus] at this; omega)) p.modulusBound

private theorem power_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h32 : 32 ∈ slots) (h36 : 36 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (odd : p.P % 2 = 1) :
    RelCT isa (fun s t => PowerInput p slots yb xb1 s ∧ PowerInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt
        (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) 36 40 44) (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  let correct := fun o a b ho ha hb z input => backend.correct z (base := p.base) (len := p.len) (w := p.w)
    (o := o) (a := a) (b := b) input ho ha hb
  let K := TwoExp.sharedMontgomery p.base s.sp p.len p.w backend.name backend.mul correct backend.stackOk
  have timing : TwoExp.MontgomeryTiming K :=
    TwoExp.sharedMontgomeryTiming p.base s.sp p.len p.w backend.name backend.mul correct backend.stackOk
      (fun _ _ _ ho ha hb => backend.rawCT ho ha hb)
  have separate : ∀ r ∈ [⟨State.addr p.base, 8 * p.len⟩, FrameStack.belowA s.sp 48],
      Region.Disjoint ⟨State.addr (p.slotValue 40), xb1.length⟩ r := by
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r; exact h.1.exponent.separate
    · have eq := List.mem_singleton.mp hr; subst r; exact h.1.calls.scalarBelow
  have run := (sharedCheckPublicPowerAt_ct K timing stable h36 h40 h44 h32
    peerLength positive fits count length odd separate).mono
    (P' := fun (a b : State) => (PowerInput p slots yb xb1 a ∧ a.sp = s.sp) ∧
      (PowerInput p slots yb xb2 b ∧ b.sp = s.sp) ∧ a.sp = b.sp)
    (fun _ _ hab => ⟨⟨hab.1.1.toExchangePowerInput.toPowerAtInput, hab.1.1.calls.stack, hab.1.2⟩,
      ⟨hab.2.1.1.toExchangePowerInput.toPowerAtInput, hab.2.1.1.calls.stack, hab.2.1.2⟩, hab.2.2⟩)
    (fun _ _ hx => hx)
  exact run s t tr1 tr2 u v ⟨⟨h.1,rfl⟩,⟨h.2.1,h.2.2.symm⟩,h.2.2⟩ e1 e2

theorem main_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length)
    (large : 1 < p.P) (odd : p.P % 2 = 1)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) :
    RelCT isa (fun s t => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  have prepare := (domainNormalizedPrepareAt24_ct backend stable h0 h24 h32 large odd normalized).mono
    (P' := fun (s t : State) => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨⟨h.1.context,h.1.calls.toDomainCallMemory⟩,
      ⟨h.2.1.context,h.2.1.calls.toDomainCallMemory⟩,h.2.2⟩) (fun _ _ h => h)
  have ranges := (inRange_ct (base := p.base) (len := p.len) (w := p.w)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => ExchangePowered p slots s ∧ ExchangePowered p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready,h.2.1.ready,h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.SharedExchange.main
  exact relCT_chain prepare
    (fun s h => prepare_power backend s h stable h0 h24 h32 peerLength large odd normalized)
    (fun s h => prepare_power backend s h stable h0 h24 h32 peerLength large odd normalized)
    (relCT_chain (power_ct backend stable h32 h36 h40 h44 peerLength positive fits count length odd)
      (fun s h => power_finish backend s h stable h32 h36 h40 h44 peerLength positive fits count odd)
      (fun s h => power_finish backend s h stable h32 h36 h40 h44 peerLength
        (by rw [←length]; exact positive) (by rw [←length]; exact fits) (by rw [←length]; exact count) odd)
      (relCT_chain ranges (fun s h => exchangeRange_finish s h stable odd)
        (fun s h => exchangeRange_finish s h stable odd) (exchangeFinish_ct stable h4 h32 saved)))

end VG.Proof.Ffdh.Arm.SharedExchange
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedExchangeBodyCT.lean`, which only this module imported.
section

/-! Invalid-domain handling and the shared-secret body reveal no private scalar data. -/

section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem body_ct (backend : MontBackend) {p : Inputs} {slots : List Nat} {yb xb1 xb2 : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (peerLength : yb.length = p.k) (positive : 0 < xb1.length) (fits : xb1.length < 2 ^ 32)
    (count : p.slotValue 44 = BitVec.ofNat 32 xb1.length) (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.head (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) (fun _ _ => True) := by
  let Q := fun (xb : List Byte) (s : State) => MainInput p (60 :: 56 :: slots) yb xb s ∧
    s.z = Spec.Rsa.modulusValid p.P p.k
  have head := (head_ct stable h0 h24 h32).mono
    (P' := fun (s t : State) => MainInput p slots yb xb1 s ∧ MainInput p slots yb xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.context, h.2.1.context, h.2.2⟩) (fun _ _ h => h)
  have wp (s : State) {xb : List Byte} (h : MainInput p slots yb xb s) :
      WP isa (.seq (.block (VG.Impl.Ffdh.Arm.Domain.prepareArgs 24 ++ VG.Impl.Ffdh.Arm.Domain.domainPointers))
        (.block VG.Impl.Bignum.Arm.modulusCheck)) s (Q xb) := by
    refine WP.mono (head_ok s h.context stable h0 h24 h32) ?_
    rintro u ⟨context, zero, frame, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨⟨context, h.peer.after_frame frame rest (sourceSep h.peerStack),
      h.scalar.after_frame frame rest (sourceSep h.scalarStack), h.output.after rest,
      by rw [rest.sp]; exact h.peerStack, by rw [rest.sp]; exact h.scalarStack,
      h.workspaceSep, by rw [rest.sp]; exact h.stackSep⟩, h.calls.after rest⟩, zero⟩
  have stable' : stableSlots (60 :: 56 :: slots) = true := by
    change (true && (true && stableSlots slots)) = true
    rw [Bool.true_and, Bool.true_and, stable]
  have saved' : ∀ d ∈ 60 :: 56 :: slots, d + 4 ≤ 64 ∨ 68 ≤ d := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact saved d hd
  have branches : RelCT isa (fun s t => Q xb1 s ∧ Q xb2 t ∧ s.sp = t.sp)
      (.ite .eq (VG.Impl.Ffdh.Arm.SharedExchange.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (VG.Impl.Ffdh.Arm.Domain.ret 0)) (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some s.z = some t.z; rw [h.1.2, h.2.1.2])
    · intro s t tr1 tr2 u v h e1 e2
      have valid : Spec.Rsa.modulusValid p.P p.k = true := by
        have selected := h.2
        change some s.z = some true at selected
        rw [h.1.1.2] at selected
        exact Option.some.inj selected
      have facts := VG.Proof.Bignum.valid_facts valid p.minLength
      exact main_ct backend stable' (by simp [h0]) (by simp [h4]) (by simp [h24])
        (by simp [h32]) (by simp [h36]) (by simp [h40]) (by simp [h44]) saved'
        peerLength positive fits count length facts.2.1 facts.1 facts.2.2 s t tr1 tr2 u v
        ⟨h.1.1.1, h.1.2.1.1, h.1.2.2⟩ e1 e2
    · exact (ret_ct 0).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply RelCT.assoc
  exact relCT_chain head (fun s h => wp s h) (fun s h => wp s h) branches

end VG.Proof.Ffdh.Arm.SharedExchange
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedExchangeFnCT.lean`, which only this module imported.
section

/-! The complete callable shared-secret computation is constant time in the private scalar. -/

section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

theorem fn_ct (backend : MontBackend) {p : Inputs} {yb xb1 xb2 : List Byte} (length : xb1.length = xb2.length) :
    RelCT isa (fun s t => FnInput p yb xb1 s ∧ FnInput p yb xb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.SharedExchange.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) (fun _ _ => True) := by
  let P := fun (xb : List Byte) (a : State) => ∃ s, FnInput p yb xb s ∧ a = entered s
  have entry := exchangeEntry_ct.mono
    (P' := fun (s t : State) => P xb1 s ∧ P xb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ h => h)
  have wp (a : State) {xb : List Byte} (h : P xb a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry) a
        (MainInput p [0, 36, 44, 40, 32, 28, 24, 4] yb xb) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (exchangeEntry_ok (entered s) input.input.args input.input.incoming input.input.out input.input.domain input.input.domainLength)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩
    have sourceSep {src : BitVec 32} {bs : List Byte}
        (sep : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr (entered s).sp, 72⟩)
        (r : Region) (hr : r ∈ [⟨State.addr (entered s).sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
      rw [List.mem_singleton] at hr; subst r; exact sep
    exact ⟨⟨context, input.input.peer.after_frame frame rest (sourceSep input.input.peerStack),
      input.input.scalar.after_frame frame rest (sourceSep input.input.scalarStack), input.input.output.after rest,
      by rw [rest.sp]; exact input.input.peerStack, by rw [rest.sp]; exact input.input.scalarStack,
      input.input.workspaceSep, by rw [rest.sp]; exact input.input.stackSep⟩, input.calls.after rest⟩
  unfold VG.Impl.Ffdh.Arm.SharedExchange.code
  apply framed_ct (fun _ _ h => ⟨h.1.input.stackFits, h.2.1.input.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  have body := relCT_chain entry (fun a h => wp a h) (fun a h => wp a h)
    (body_ct backend (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro d hd; revert d; decide) related.1.input.peerLength related.1.input.positive related.1.input.scalarFit related.1.input.scalarCount length)
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm.SharedExchange
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm

theorem contract_ct (backend : Bignum.Arm.MontBackend) : ConstantTime isa (Spec.Ffdh.exchangeContract abi 176).pre
    (Spec.Ffdh.exchangeContract abi 176).pub (VG.Impl.Ffdh.Arm.SharedExchange.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, out, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.exchangeContract abi 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 0).toNat := by
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, p7, _, p9, p10⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p2, ← p3, ← p7, ← p4] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, _⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := input t ht (p := p) (yb := yb) (xb := xb2)
    (p9.symm.trans base) (p0.symm.trans out) (p2.symm.trans domain) (p7.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p4]; exact count) (by rw [← p10]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    exact (fn_ct backend (by rw [xLength, x2Length]) s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p3, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 3)) (stackArg s 0).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

end VG.Proof.Ffdh.Arm.SharedExchange

end

end


/-! Native ARMv7 shared-secret computation is verified against the shared FFDH API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm

private def exchangeSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 128 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 64 else if a = 0x8005 then 0x30 else if a = 0x8008 then 1 else
    if a = 0x800d then 0x31 else if a = 0x8010 then 64 else if a = 0x8015 then 0x40 else
    if a = 0x8018 then 0x20 else if a = 0x8019 then 4 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x8000, 28⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩]

theorem sat : ∃ s, (Spec.Ffdh.exchangeContract abi 176).pre s := by
  sig_implies_sat [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, Spec.Ffdh.pLenValid,
    Spec.Ffdh.domainLenValid, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [exchangeSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.scratchWords] using exchangeSat

theorem verified (backend : VG.Proof.Bignum.Arm.MontBackend) : Verified target (code backend)
    (Spec.Ffdh.exchangeContract abi 176) :=
  ⟨correct backend, contract_ct backend, sat⟩

end VG.Proof.Ffdh.Arm.SharedExchange

end

end

/-! The backend's caller transformation preserves shared Montgomery calls. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm VG.Proof.Bignum.Arm

def calledCode (b : MontBackend) : Prog isa := b.caller.code (code b)

theorem called_verified (b : MontBackend) :
    Verified target (calledCode b) (Spec.Ffdh.exchangeContract abi 176) :=
  b.caller.verified (verified b)

end VG.Proof.Ffdh.Arm.SharedExchange
