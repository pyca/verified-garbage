module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore

/-! ### `Ffdh.Arm.ExchangeEntry`, which this module and modules that import it used -/

section

/-! Retain the shared-secret ABI's output, domain, scalar, peer, and workspace arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure ExchangeIncoming (p : Inputs) (s : State) : Prop where
  modulus : IncomingWord (BitVec.ofNat 32 p.k) 128 s
  scalar : IncomingWord p.privateValue 132 s
  scalarCount : IncomingWord (BitVec.ofNat 32 p.privateLength) 136 s
  peer : IncomingWord p.publicValue 140 s
  scratch : IncomingWord p.base 148 s

theorem exchangeEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : ExchangeIncoming p s) (out : s.gpr .r0 = p.output)
    (domain : s.gpr .r2 = p.domain) (domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.Exchange.entry) s fun t =>
      Context p [0, 36, 44, 40, 32, 28, 24, 4] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.entry VG.Impl.Ffdh.Arm.Domain.st
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
  refine wp_retain_incoming .r3 (by decide) args6 (by decide)
    (incoming.peer.after (by decide) frame6 allRest6) (by decide) (by decide) (by decide) stack6
    fun s7 args7 stepFrame7 stepRest7 value7 stack7 => ?_
  have allRest7 := allRest6.trans (stepRest7.mono (by simp [roundClobbers]))
  rw [allRest6.sp] at stepFrame7
  have frame7 := frame6.trans stepFrame7
  refine wp_retain_incoming .r0 (by decide) args7 (by decide)
    (incoming.scratch.after (by decide) frame7 allRest7) (by decide) (by decide) (by decide) stack7
    fun s8 args8 stepFrame8 stepRest8 value8 stack8 => WP.block_nil ?_
  refine ⟨⟨args8, value8⟩, ?_⟩
  rw [allRest7.sp] at stepFrame8
  exact frame7.trans stepFrame8

end VG.Proof.Ffdh.Arm

end

end

/-! AAPCS shared-secret computation with native validation and output handling. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem exchangeEntered_ok (s : State) {p : Inputs} {yb xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : ExchangeIncoming p s)
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
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.Exchange.main)) s fun t =>
        (Spec.Rsa.modulusValid p.P p.k = true → exchangeResult p yb xb t) ∧
        Frame (exchangeWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (exchangeEntry_ok s h incoming out domain domainLength)) ?_
  rintro u ⟨⟨context, frame⟩, rest⟩
  have sourceSep {src : BitVec 32} {bs : List Byte}
      (separate : Region.Disjoint ⟨State.addr src, bs.length⟩ ⟨State.addr s.sp, 72⟩)
      (r : Region) (hr : r ∈ [⟨State.addr s.sp, 72⟩]) : (⟨State.addr src, bs.length⟩ : Region).Disjoint r := by
    rw [List.mem_singleton] at hr; subst r; exact separate
  refine WP.mono (exchangeBody_ok u context (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro d hd; revert d; decide)
    (peer.after_frame frame rest (sourceSep peerStack)) peerLength
    (scalar.after_frame frame rest (sourceSep scalarStack)) positive scalarFit scalarCount
    (by rw [rest.sp]; exact peerStack) (by rw [rest.sp]; exact scalarStack) (output.after rest)
    workspaceSep (by rw [rest.sp]; exact stackSep)) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (exchangeWrites p s) s.mem u.mem := frame.mono (by simp [exchangeWrites])
  exact ⟨result, entryFrame.trans (by simpa only [exchangeWrites, rest.sp] using frameT)⟩

structure ExchangeFnInput (p : Inputs) (yb xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : ExchangeIncoming p (entered s)
  out : s.gpr .r0 = p.output
  domain : s.gpr .r2 = p.domain
  domainLength : s.gpr .r3 = BitVec.ofNat 32 p.dom.length
  peer : Octets p.base p.publicValue p.len yb (entered s)
  peerLength : yb.length = p.k
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarFit : xb.length < 2 ^ 32
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  peerStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  output : OutputBuffer p.output p.k (entered s)
  workspaceSep : Region.Disjoint ⟨State.addr p.base, 8 * p.len⟩ ⟨State.addr p.output, p.k⟩
  stackSep : Region.Disjoint ⟨State.addr (entered s).sp, 72⟩ ⟨State.addr p.output, p.k⟩
  saved : ∀ r ∈ exchangeWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem exchangeFn_ok (s : State) {p : Inputs} {yb xb : List Byte} (h : ExchangeFnInput p yb xb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.Exchange.code s fun t => abiPreserved s t ∧
      (Spec.Rsa.modulusValid p.P p.k = true → exchangeResult p yb xb t) := by
  unfold VG.Impl.Ffdh.Arm.Domain.Exchange.code
  refine framed_of_separate _ s h.stackFits (exchangeWrites p (entered s))
    (fun m status => Spec.Rsa.modulusValid p.P p.k = true → status = (if sharedAccepted p yb xb then 1 else 0) ∧
      Spec.Rsa.bytesAt m (State.addr p.output) p.k =
        (if sharedAccepted p yb xb then Spec.Rsa.i2osp (sharedValue p yb xb) p.k else List.replicate p.k 0)) h.saved ?_
  refine WP.mono (exchangeEntered_ok (entered s) h.args h.incoming h.out h.domain h.domainLength
    h.peer h.peerLength h.scalar h.positive h.scalarFit h.scalarCount h.peerStack h.scalarStack h.output
    h.workspaceSep h.stackSep) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
