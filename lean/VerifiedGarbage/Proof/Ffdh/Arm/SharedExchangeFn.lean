module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeEntry
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeFn
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeBody
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeMemory

import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeMain
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Framework.Block
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
  refine WP.mono (entered_ok backend (entered s) h.input.args h.input.incoming h.calls h.input.out h.input.domain h.input.domainLength
    h.input.peer h.input.peerLength h.input.scalar h.input.positive h.input.scalarFit h.input.scalarCount h.input.peerStack h.input.scalarStack h.input.output
    h.input.workspaceSep h.input.stackSep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm.SharedExchange
