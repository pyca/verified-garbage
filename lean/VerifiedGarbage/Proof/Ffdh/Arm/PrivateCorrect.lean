module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore

/-! ### `Ffdh.Arm.PrivatePre`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.PrivateFn`, which this module and modules that import it used -/

section

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
  obtain rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  obtain args0 := h.of_mem moved.mem rest0
  obtain frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  obtain stack0 : s0.gpr .r12 = s0.sp := by rw [moved.gpr, moved.sp, BitVec.add_zero]
  refine wp_store_arg .r0 24 args0 (by decide) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans domain) stack0 fun s1 args1 stepFrame1 stepRest1 => ?_
  obtain rest1 := rest0.trans (stepRest1.mono (by simp))
  obtain stack1 := (stepRest1.gpr .r12 (by simp)).trans (stack0.trans stepRest1.sp.symm)
  rw [rest0.sp] at stepFrame1
  obtain frame1 := frame0.trans stepFrame1
  refine wp_store_arg .r1 28 args1 (by decide) (by decide) (by decide)
    ((rest1.gpr .r1 (by simp)).trans domainLength) stack1 fun s2 args2 stepFrame2 stepRest2 => ?_
  obtain rest2 := rest1.trans (stepRest2.mono (by simp))
  obtain stack2 := (stepRest2.gpr .r12 (by simp)).trans (stack1.trans stepRest2.sp.symm)
  rw [rest1.sp] at stepFrame2
  obtain frame2 := frame1.trans stepFrame2
  refine wp_store_arg .r2 32 args2 (by decide) (by decide) (by decide)
    ((rest2.gpr .r2 (by simp)).trans count) stack2 fun s3 args3 stepFrame3 stepRest3 => ?_
  obtain rest3 := rest2.trans (stepRest3.mono (by simp))
  obtain stack3 := (stepRest3.gpr .r12 (by simp)).trans (stack2.trans stepRest3.sp.symm)
  rw [rest2.sp] at stepFrame3
  obtain frame3 := frame2.trans stepFrame3
  refine wp_store_arg .r3 36 args3 (by decide) (by decide) (by decide)
    ((rest3.gpr .r3 (by simp)).trans publicValue) stack3 fun s4 args4 stepFrame4 stepRest4 => ?_
  obtain rest4 := rest3.trans (stepRest4.mono (by simp))
  obtain stack4 := (stepRest4.gpr .r12 (by simp)).trans (stack3.trans stepRest4.sp.symm)
  rw [rest3.sp] at stepFrame4
  obtain frame4 := frame3.trans stepFrame4
  obtain allRest4 : Rest roundClobbers s s4 := rest4.mono (by simp [roundClobbers])
  refine wp_retain_incoming .r3 (by decide) args4 (by decide)
    (incoming.scalar.after (by decide) frame4 allRest4) (by decide) (by decide) (by decide) stack4
    fun s5 args5 stepFrame5 stepRest5 value5 stack5 => ?_
  obtain allRest5 := allRest4.trans (stepRest5.mono (by simp [roundClobbers]))
  rw [allRest4.sp] at stepFrame5
  obtain frame5 := frame4.trans stepFrame5
  refine wp_retain_incoming .r3 (by decide) args5 (by decide)
    (incoming.scalarCount.after (by decide) frame5 allRest5) (by decide) (by decide) (by decide) stack5
    fun s6 args6 stepFrame6 stepRest6 value6 stack6 => ?_
  obtain allRest6 := allRest5.trans (stepRest6.mono (by simp [roundClobbers]))
  rw [allRest5.sp] at stepFrame6
  obtain frame6 := frame5.trans stepFrame6
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
  obtain valueU := value.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact valueStack)
  obtain valueStackU : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr u.sp, 72⟩ := by
    rw [restU.sp]; exact valueStack
  obtain scalarU := scalar.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr; subst r; exact scalarStack)
  refine WP.mono (privateBody_ok u contextU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) valueU length scalarU positive scalarLength scalarCount
    (by rw [restU.sp]; exact scalarStack) valueStackU) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  obtain entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
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

end

end

/-! The shared imported-private-key signature supplies native frame and buffer invariants. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem private_input (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s)
    {p : Inputs} {yb xb : List Byte}
    (base : stackArg s 3 = p.base) (domain : s.gpr .r0 = p.domain) (peer : s.gpr .r3 = p.publicValue)
    (scalar : stackArg s 1 = p.privateValue) (count : (s.gpr .r2).toNat = p.k)
    (capacity : (stackArg s 4).toNat = p.len) (privateCount : (stackArg s 2).toNat = p.privateLength)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (peerBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb)
    (scalarBytes : Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb) :
    PrivateFnInput p yb xb s := by
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, xS, sArgs, stackDom, stackY, stackX, stackS, stackArgs,
    domFit, yFit, xFit, sFit, _, _, yLen, xPositive, xMax, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have yLength : yb.length = p.k := by
    have eq := congrArg List.length peerBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [yLen, count] at rd yS stackY yFit
  rw [count] at xMax
  rw [privateCount] at rd xS stackX xFit xPositive xMax
  rw [domain, domLen] at rd domS stackDom domFit
  rw [peer] at rd yS stackY yFit
  rw [scalar] at rd xS stackX xFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS xS yS sArgs stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackX stackY stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domainRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have peerRead : InRegions (s.rd ++ s.wr) (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have scalarRead : InRegions (s.rd ++ s.wr) (State.addr p.privateValue) p.privateLength :=
    ⟨⟨State.addr p.privateValue, p.privateLength⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have rootDomain : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domainRead, domS, by rw [← domLen]; exact domainBytes⟩
  have rootPeer : Octets p.base p.publicValue p.len yb s :=
    ⟨by rw [yLength]; exact yFit, by rw [yLength]; exact peerRead,
      by rw [yLength]; exact yS, by rw [yLength]; exact peerBytes⟩
  have rootScalar : Octets p.base p.privateValue p.len xb s :=
    ⟨by rw [xLength]; exact xFit, by rw [xLength]; exact scalarRead,
      by rw [xLength]; exact xS, by rw [xLength]; exact scalarBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets rootDomain stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have argAddr (i : Nat) (hi : i < 5) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega_using [argFit, hi])
  have argSub (i : Nat) (hi : i < 5) :
      (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨stackArgAddr s 0, 20⟩ := by
    rw [argStart, argAddr i hi]; exact Offset.sub_base _ (by omega_using [hi])
  have incoming (i : Nat) (hi : i < 5) : IncomingWord (stackArg s i) (128 + 4 * i) (entered s) :=
    enteredIncoming s stackFit (by omega_using [argFit, hi])
      ⟨⟨stackArgAddr s 0, 20⟩, List.mem_append_left _ (by rw [rd]; simp), by
        rw [argStart, argAddr i hi]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
      (stackArgs.sub_right (argSub i hi)) rfl
  have nativeIncoming : PrivateIncoming p (entered s) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← scalar]; exact incoming 1 (by decide)
    · have h := incoming 2 (by decide)
      rw [← privateCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h
    · rw [← base]; exact incoming 3 (by decide)
  refine ⟨stackFit, args, nativeIncoming, domain, ?_, ?_, peer,
    entered_octets rootPeer stackFit (by rw [yLength]; exact stackY), yLength,
    entered_octets rootScalar stackFit (by rw [xLength]; exact stackX),
    by rw [xLength]; omega_using [xPositive], by rw [xLength]; exact xMax, ?_, ?_, ?_, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat 32 p.privateLength = _; rw [xLength]
  · rw [xLength]; exact stackX.symm.sub_right (locals_sub_reserved s stackFit)
  · rw [yLength]; exact stackY.symm.sub_right (locals_sub_reserved s stackFit)
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm

end

end

/-! Native callable imported-private-key validation satisfies the shared FFDH result contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem private_data (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s) :
    ∃ (p : Inputs) (yb xb : List Byte), stackArg s 3 = p.base ∧ s.gpr .r0 = p.domain ∧
      s.gpr .r3 = p.publicValue ∧ stackArg s 1 = p.privateValue ∧ (s.gpr .r2).toNat = p.k ∧
      (stackArg s 4).toNat = p.len ∧ (stackArg s 2).toNat = p.privateLength ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb ∧
      Spec.Rsa.bytesAt s.mem (State.addr p.privateValue) p.privateLength = xb ∧ PrivateFnInput p yb xb s := by
  have original := pre
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bounds, domainLen, _, _, _, space⟩ := pre
  let dom := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  have domLength : dom.length = (s.gpr .r1).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  let p : Inputs := {
    base := stackArg s 3
    domain := s.gpr .r0
    publicValue := s.gpr .r3
    privateValue := stackArg s 1
    output := 0
    entropy := 0
    len := (stackArg s 4).toNat
    k := (s.gpr .r2).toNat
    privateLength := (stackArg s 2).toNat
    hasQ := decide ((s.gpr .r1).toNat = 3 * (s.gpr .r2).toNat)
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
  let yb := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (s.gpr .r2).toNat
  let xb := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  exact ⟨p, yb, xb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    private_input s original (p := p) (yb := yb) (xb := xb) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩

theorem private_correct (s : State) (pre : (Spec.Ffdh.checkPrivateContract abi 128).pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.code s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.checkPrivateContract abi 128).post s t := by
  obtain ⟨p, yb, xb, _, domain, peer, scalar, count, _, privateCount,
    domainBytes, peerBytes, scalarBytes, input⟩ := private_data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := privateFn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  have length : (stackArg s 0).toNat = (s.gpr .r2).toNat := by
    sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := pre
    exact length
  sig_post [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [State.addr] at domainBytes peerBytes scalarBytes
  simp only [length, count, domain, peer, scalar, privateCount, domainBytes, peerBytes, scalarBytes]
  intro valid
  rw [result]
  exact checkedPrivateFlag_spec p yb xb valid

end VG.Proof.Ffdh.Arm
