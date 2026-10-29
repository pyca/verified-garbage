module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord

import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
/-! The native private-key check, from its entry through AAPCS restoration. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/PrivateEntry.lean`, which only this module imported.
section

/-! Retain the imported private-key ABI's public and scalar arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PrivateIncoming (p : Inputs) (s : State) : Prop where
  scalar : IncomingWord p.privateValue 132 s
  scalarCount : IncomingWord (BitVec.ofNat 32 p.privateLength) 136 s
  scratch : IncomingWord p.base 140 s

theorem privateEntry_ok (s : State) {p : Inputs} (h : ArgumentMemory p [] s)
    (incoming : PrivateIncoming p s) (domain : s.gpr .r0 = p.domain)
    (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length) (count : s.gpr .r2 = BitVec.ofNat 32 p.k)
    (publicValue : s.gpr .r3 = p.publicValue) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry) s fun t =>
      Context p [0, 44, 40, 36, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  have rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  have args0 := h.of_mem moved.mem rest0
  have frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  have stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 24 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans domain) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  have rest1 := rest0.trans (stepRest1.mono (by simp))
  have stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  have frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r1 28 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r1 (by simp)).trans domainLength) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  have rest2 := rest1.trans (stepRest2.mono (by simp))
  have stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  have frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r2 32 args2 (by decide) (by decide) (by decide)
    ((rest2.gpr .r2 (by simp)).trans count) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  have rest3 := rest2.trans (stepRest3.mono (by simp))
  have stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  have frame3 := frame2.trans stepFrame3
  refine wp_store_arg .r3 36 args3 (by decide) (by decide) (by decide)
    ((rest3.gpr .r3 (by simp)).trans publicValue) stack3 fun s4 args4 stepFrame4 stepRest4 => ?_
  have rest4 := rest3.trans (stepRest4.mono (by simp))
  have stack4 := (stepRest4.gpr .r12 (by simp)).trans (stack3.trans stepRest4.sp.symm)
  rw [rest3.sp] at stepFrame4
  have frame4 := frame3.trans stepFrame4
  have allRest4 : Rest roundClobbers s s4 := rest4.mono (by simp [roundClobbers])
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

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem privateEntered_ok (s : State) {p : Inputs} {yb xb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : PrivateIncoming p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (scalar : Octets p.base p.privateValue p.len xb s) (positive : 0 < xb.length)
    (scalarLength : xb.length ≤ p.k) (scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length)
    (scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr s.sp, 72⟩)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckPrivate.entry)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPrivate.main)) s fun t =>
      t.gpr .r0 = checkedPrivateFlag p yb xb ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (privateEntry_ok s h incoming domain domainLength count publicValue)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact valueStack)
  have valueStackU : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr u.sp, 72⟩ := by
    rw [restU.sp]; exact valueStack
  have scalarU := scalar.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r; exact scalarStack)
  refine WP.mono (privateBody_ok u contextU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) valueU length scalarU positive scalarLength scalarCount
    (by rw [restU.sp]; exact scalarStack) valueStackU) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  have entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

structure PrivateFnInput (p : Inputs) (yb xb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : PrivateIncoming p (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  value : Octets p.base p.publicValue p.len yb (entered s)
  length : yb.length = p.k
  scalar : Octets p.base p.privateValue p.len xb (entered s)
  positive : 0 < xb.length
  scalarLength : xb.length ≤ p.k
  scalarCount : p.slotValue 44 = BitVec.ofNat 32 xb.length
  scalarStack : Region.Disjoint ⟨State.addr p.privateValue, xb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem privateFn_ok (s : State) {p : Inputs} {yb xb : List Byte} (h : PrivateFnInput p yb xb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedPrivateFlag p yb xb := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedPrivateFlag p yb xb) h.saved ?_
  refine WP.mono (privateEntered_ok (entered s) h.args h.incoming h.domain h.domainLength
    h.count h.publicValue h.value h.length h.scalar h.positive h.scalarLength h.scalarCount h.scalarStack h.valueStack) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm
