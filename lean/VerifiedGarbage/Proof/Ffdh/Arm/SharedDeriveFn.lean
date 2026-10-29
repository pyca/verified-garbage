module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveMain
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive

import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Ffdh.Arm.Head
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
/-! The AAPCS derivation of an imported scalar's public value. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveEntry.lean`, which only this module imported.
section

/-! Retain the public-value derivation's output, domain, scalar, and workspace arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure DeriveIncoming (p : Inputs) (s : State) : Prop where
  modulus : IncomingWord (BitVec.ofNat 32 p.k) 128 s
  scalar : IncomingWord p.privateValue 132 s
  scalarCount : IncomingWord (BitVec.ofNat 32 p.privateLength) 136 s
  scratch : IncomingWord p.base 140 s

theorem deriveEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : DeriveIncoming p s) (out : s.gpr .r0 = p.output)
    (domain : s.gpr .r2 = p.domain) (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.SharedDerive.entry) s fun t =>
      Context p [0, 44, 40, 32, 28, 24, 4] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.SharedDerive.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  have rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  have args0 := h.of_mem moved.mem rest0
  have frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  have stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 4 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans out) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  have rest1 := rest0.trans (stepRest1.mono (by simp))
  have stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  have frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r2 24 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r2 (by simp)).trans domain) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  have rest2 := rest1.trans (stepRest2.mono (by simp))
  have stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  have frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r3 28 args2 (by decide) (by decide) (by decide)
    ((rest2.gpr .r3 (by simp)).trans domainLength) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  have rest3 := rest2.trans (stepRest3.mono (by simp))
  have stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  have frame3 := frame2.trans stepFrame3
  have allRest3 : Rest roundClobbers s s3 := rest3.mono (by simp [roundClobbers])
  refine wp_retain_incoming .r3 (by decide) args3 (by decide)
    (incoming.modulus.after (by decide) frame3 allRest3) (by decide) (by decide) (by decide) stack3
    fun s4 args4 stepFrame4 stepRest4 value4 stack4 => ?_
  have allRest4 := allRest3.trans (stepRest4.mono (by simp [roundClobbers]))
  rw [allRest3.sp] at stepFrame4
  have frame4 := frame3.trans stepFrame4
  refine wp_retain_incoming .r3 (by decide) args4 (by decide)
    (incoming.scalar.after (by decide) frame4 allRest4) (by decide) (by decide) (by decide) stack4
    fun s5 args5 stepFrame5 stepRest5 value5 stack5 => ?_
  have allRest5 := allRest4.trans (stepRest5.mono (by simp [roundClobbers]))
  rw [allRest4.sp] at stepFrame5
  have frame5 := frame4.trans stepFrame5
  refine wp_retain_incoming .r3 (by decide) args5 (by decide)
    (incoming.scalarCount.after (by decide) frame5 allRest5) (by decide) (by decide) (by decide) stack5
    fun s6 args6 stepFrame6 stepRest6 value6 stack6 => ?_
  have allRest6 := allRest5.trans (stepRest6.mono (by simp [roundClobbers]))
  rw [allRest5.sp] at stepFrame6
  have frame6 := frame5.trans stepFrame6
  refine wp_retain_incoming .r0 (by decide) args6 (by decide)
    (incoming.scratch.after (by decide) frame6 allRest6) (by decide) (by decide) (by decide) stack6
    fun s7 args7 stepFrame7 stepRest7 value7 stack7 => WP.block_nil ?_
  refine ⟨⟨args7, value7⟩, ?_⟩
  rw [allRest6.sp] at stepFrame7
  exact frame6.trans stepFrame7

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/SharedDeriveBody.lean`, which only this module imported.
section

/-! The derivation's body is safe for every domain encoding, and specified for valid moduli. -/

section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem body_ok (backend : MontBackend) (s : State) {p : Inputs} {slots : List Nat} {xb : List Byte}
    (h : Context p slots s) (calls : SharedExchange.CallMemory p xb.length s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h4 : 4 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.head
      (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul))) s fun t =>
      (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) ∧
      Frame (SharedExchange.writes p s) s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.head
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (head_ok s h stable h0 h24 h32) ?_
  rintro u ⟨context, zero, frame, rest⟩
  have entryFrame : Frame (SharedExchange.writes p s) s.mem u.mem :=
    frame.mono (by simp [SharedExchange.writes, exchangeWrites])
  by_cases valid : Spec.Rsa.modulusValid p.P p.k = true
  · refine WP.ite true (by change some u.z = some true; rw [zero, valid]) ?_ (by intro hf; cases hf)
    intro _
    have facts := VG.Proof.Bignum.valid_facts valid p.minLength
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
    refine WP.mono (main_ok backend u context (calls.after rest) stable' (by simp [h0]) (by simp [h4])
      (by simp [h24]) (by simp [h28]) (by simp [h32]) (by simp [h40]) (by simp [h44]) (by simp) (by simp)
      saved' facts.2.1 facts.1 facts.2.2
      (scalar.after_frame frame rest (by
        intro r hr; rw [List.mem_singleton] at hr; subst r; exact scalarStack))
      positive scalarLength scalarCount (by rw [rest.sp]; exact scalarStack) (output.after rest)
      workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
    rintro t ⟨res, frameT⟩
    exact ⟨fun _ => res, entryFrame.trans (by simpa only [SharedExchange.writes, exchangeWrites, rest.sp] using frameT)⟩
  · refine WP.ite false (by change some u.z = some false; rw [zero, Bool.eq_false_iff.mpr valid])
      (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (ret_ok u 0 (by decide)) ?_
    rintro t ⟨⟨_, mem⟩, _⟩
    exact ⟨fun hv => (valid hv).elim, by rw [mem]; exact entryFrame⟩

end VG.Proof.Ffdh.Arm.SharedDerive
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Proof.Bignum.Arm

theorem entered_ok (backend : MontBackend) (s : State) {p : Inputs} {xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : DeriveIncoming p s) (calls : SharedExchange.CallMemory p xb.length s)
    (out : s.gpr .r0 = p.output) (domain : s.gpr .r2 = p.domain)
    (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (output : OutputBuffer p.output p.k s)
    (workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.output, p.k⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.SharedDerive.entry)
      (VG.Impl.Ffdh.Arm.Domain.head
        (VG.Impl.Ffdh.Arm.SharedDerive.main (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)))) s
      fun t => (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) ∧
        Frame (SharedExchange.writes p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (deriveEntry_ok s h incoming out domain domainLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  refine WP.mono (body_ok backend u context (calls.after rest) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    (scalar.after_frame frame rest (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact scalarStack))
    positive scalarLength scalarCount (by rw [rest.sp]; exact scalarStack) (output.after rest)
    workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
  rintro t ⟨res, frameT⟩
  have entryFrame : Frame (SharedExchange.writes p s) s.mem u.mem :=
    frame.mono (by simp [SharedExchange.writes, exchangeWrites])
  exact ⟨res, entryFrame.trans (by simpa only [SharedExchange.writes, exchangeWrites, rest.sp] using frameT)⟩

structure FnInput (p : Inputs) (xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : DeriveIncoming p (entered s)
  calls : SharedExchange.CallMemory p xb.length (entered s)
  out : s.gpr .r0 = p.output
  domain : s.gpr .r2 = p.domain
  domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarLength : xb.length ≤ p.k
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  output : OutputBuffer p.output p.k (entered s)
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr (entered s).sp, 72⟩ ⟨State.addr p.output, p.k⟩
  saved : ∀ r ∈ SharedExchange.writes p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem fn_ok (backend : MontBackend) (s : State) {p : Inputs} {xb : List Byte} (h : FnInput p xb s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) s
      fun t => abiPreserved s t ∧ (Spec.Rsa.modulusValid p.P p.k = true → result p xb t) := by
  unfold VG.Impl.Ffdh.Arm.SharedDerive.code
  refine framed_of_separate _ s h.stackFits (SharedExchange.writes p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true → status = SharedDerive.status p xb ∧
      Spec.Rsa.bytesAt m (State.addr p.output) p.k =
        (open Classical in if accepted p xb then Spec.Rsa.i2osp (sharedValue p (gOctets p) xb) p.k
          else List.replicate p.k 0)) h.saved ?_
  refine WP.mono (entered_ok backend (entered s) h.args h.incoming h.calls h.out h.domain h.domainLength
    h.scalar h.positive h.scalarLength h.scalarCount h.scalarStack h.output h.workspaceSep h.stackSep) ?_
  rintro t ⟨res, frame⟩
  exact ⟨frame, res⟩

end VG.Proof.Ffdh.Arm.SharedDerive
