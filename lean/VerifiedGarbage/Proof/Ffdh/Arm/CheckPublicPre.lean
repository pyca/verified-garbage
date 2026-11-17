module

import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack

/-! ### `Ffdh.Arm.CheckPublicFn`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.CheckPublicEntry`, which this module and modules that import it used -/

section

/-! The imported-public-value ABI arguments are retained in native locals. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PublicEntryRegs (p : Inputs) (s : State) : Prop where
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  stackBase : s.gpr .r12 = s.sp

theorem PublicEntryRegs.after {p : Inputs} {s t : State}
    (h : PublicEntryRegs p s) (rest : Rest [] s t) : PublicEntryRegs p t :=
  ⟨(rest.gpr .r0 (by simp)).trans h.domain, (rest.gpr .r1 (by simp)).trans h.domainLength,
    (rest.gpr .r2 (by simp)).trans h.count, (rest.gpr .r3 (by simp)).trans h.publicValue,
    (rest.gpr .r12 (by simp)).trans (h.stackBase.trans rest.sp.symm)⟩

theorem checkPublicEntry_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s) (incoming : IncomingScratch p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) s fun t =>
      Context p [0, 36, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun u moved => ?_
  have restU : Rest [.r12] s u := moved.rest (by simp)
  have argsU := h.of_mem moved.mem restU
  have frameU : Frame [⟨State.addr s.sp, 72⟩] s.mem u.mem := by rw [moved.mem]; exact Frame.refl _ _
  have incomingU := incoming.after frameU restU
  have regsU : PublicEntryRegs p u :=
    ⟨(moved.other .r0 (by decide)).trans domain, (moved.other .r1 (by decide)).trans domainLength,
      (moved.other .r2 (by decide)).trans count, (moved.other .r3 (by decide)).trans publicValue,
      by rw [moved.gpr, moved.sp, BitVec.add_zero]⟩
  refine wp_store_arg .r0 24 argsU (by decide) (by decide) (by decide) regsU.domain regsU.stackBase fun v argsV frameV restV => ?_
  have regsV := regsU.after restV
  have incomingV := incomingU.after frameV restV
  rw [restU.sp] at frameV
  have fullV := frameU.trans frameV
  refine wp_store_arg .r1 28 argsV (by decide) (by decide) (by decide) regsV.domainLength regsV.stackBase fun w argsW frameW restW => ?_
  have regsW := regsV.after restW
  have incomingW := incomingV.after frameW restW
  rw [restV.sp, restU.sp] at frameW
  have fullW := fullV.trans frameW
  refine wp_store_arg .r2 32 argsW (by decide) (by decide) (by decide) regsW.count regsW.stackBase fun x argsX frameX restX => ?_
  have regsX := regsW.after restX
  have incomingX := incomingW.after frameX restX
  rw [restW.sp, restV.sp, restU.sp] at frameX
  have fullX := fullW.trans frameX
  refine wp_store_arg .r3 36 argsX (by decide) (by decide) (by decide) regsX.publicValue regsX.stackBase fun y argsY frameY restY => ?_
  have regsY := regsX.after restY
  have incomingY := incomingX.after frameY restY
  rw [restX.sp, restW.sp, restV.sp, restU.sp] at frameY
  have fullY := fullX.trans frameY
  refine wp_loadStack (a := off (State.addr y.sp) 132) (by decide)
    (addr_add (by have := incomingY.fits; omega_using [this])) incomingY.readable fun z loaded => ?_
  have restZ : Rest [.r0] y z := loaded.rest (by simp)
  have argsZ := argsY.of_mem loaded.mem restZ
  have baseZ : z.gpr .r0 = p.base := loaded.gpr.trans incomingY.value
  have spZ : z.gpr .r12 = z.sp := (loaded.other .r12 (by decide)).trans (regsY.stackBase.trans loaded.sp.symm)
  refine wp_store_arg .r0 0 argsZ (by decide) (by decide) (by decide) baseZ spZ fun t argsT frameT restT => WP.block_nil ?_
  refine ⟨⟨argsT, (restT.gpr .r0 (by simp)).trans baseZ⟩, ?_⟩
  rw [restZ.sp, restY.sp, restX.sp, restW.sp, restV.sp, restU.sp] at frameT
  rw [loaded.mem] at frameT
  exact fullY.trans frameT

end VG.Proof.Ffdh.Arm

end

end

/-! The native public-value check, from its entry through AAPCS restoration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem checkPublicEntered_ok (s : State) {p : Inputs} {yb : List Byte}
    (h : ArgumentMemory p [] s) (incoming : IncomingScratch p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue)
    (value : Octets p.base p.publicValue p.len yb s) (length : yb.length = p.k)
    (valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr s.sp, 72⟩) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry)
      (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckPublic.main)) s fun t =>
      t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono (withAllRest (checkPublicEntry_ok s h incoming domain domainLength count publicValue)) ?_
  rintro u ⟨⟨contextU, frameU⟩, restU⟩
  have valueU := value.after_frame frameU restU (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact valueStack)
  have valueStackU : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr u.sp, 72⟩ := by
    rw [restU.sp]; exact valueStack
  refine WP.mono (checkPublicBody_ok u contextU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) valueU length valueStackU) ?_
  rintro t ⟨result, frameT⟩
  refine ⟨result, ?_⟩
  have entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact entryFrame.trans frameT

structure CheckPublicFnInput (p : Inputs) (yb : List Byte) (s : State) : Prop where
  stackFits : 128 ≤ s.sp.toNat
  args : ArgumentMemory p [] (entered s)
  incoming : IncomingScratch p (entered s)
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  value : Octets p.base p.publicValue p.len yb (entered s)
  length : yb.length = p.k
  valueStack : Region.Disjoint ⟨State.addr p.publicValue, yb.length⟩ ⟨State.addr (entered s).sp, 72⟩
  saved : ∀ r ∈ bodyWrites p (entered s), (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint r

theorem checkPublicFn_ok (s : State) {p : Inputs} {yb : List Byte} (h : CheckPublicFnInput p yb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPublic.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedPublicFlag p (Spec.Rsa.os2ip yb) := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedPublicFlag p (Spec.Rsa.os2ip yb)) h.saved ?_
  refine WP.mono (checkPublicEntered_ok (entered s) h.args h.incoming h.domain h.domainLength
    h.count h.publicValue h.value h.length h.valueStack) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm

end

end

/-! The shared signature supplies the native public-check frame and buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem checkPublic_input (s : State) (pre : (Spec.Ffdh.checkPublicContract abi 128).pre s)
    {p : Inputs} {yb : List Byte}
    (base : stackArg s 1 = p.base) (domain : s.gpr .r0 = p.domain) (publicValue : s.gpr .r3 = p.publicValue)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 2).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom)
    (publicBytes : Spec.Rsa.bytesAt s.mem (State.addr p.publicValue) p.k = yb) :
    CheckPublicFnInput p yb s := by
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argFit, rd, wr, domS, yS, sArgs, stackDom, stackY, stackS, stackArgs,
    domFit, yFit, sFit, _, _, yLen, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  have length : yb.length = p.k := by
    have eq := congrArg List.length publicBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  rw [yLen, count] at rd yS stackY yFit
  rw [domain] at rd domS stackDom domFit
  rw [publicValue] at rd yS stackY yFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS yS sArgs stackS sFit
  rw [domLen] at rd domS stackDom domFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackY stackS stackArgs
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have valueRead : InRegions (s.rd ++ s.wr) (State.addr p.publicValue) p.k :=
    ⟨⟨State.addr p.publicValue, p.k⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have domOctets : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domRead, domS, by rw [← domLen]; exact domainBytes⟩
  have valueOctets : Octets p.base p.publicValue p.len yb s :=
    ⟨by rw [length]; exact yFit, by rw [length]; exact valueRead,
      by rw [length]; exact yS, by rw [length]; exact publicBytes⟩
  have locals := entered_locals s stackFit stackS
  have domEntered := entered_octets domOctets stackFit stackDom
  have valueEntered := entered_octets valueOctets stackFit (by rw [length]; exact stackY)
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, locals, domEntered,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  have argAddr : stackArgAddr s 1 = off (State.addr s.sp) 4 := VG.Arm.addr_add (by omega_using [argFit])
  have argStart : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have contains : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 1) 4 := by
    rw [argStart, argAddr]
    exact Offset.contains_base _ (by decide) (by decide)
  have argRead : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 4 :=
    ⟨⟨stackArgAddr s 0, 12⟩, List.mem_append_left _ (by rw [rd]; simp), contains⟩
  have nativeRoom : (entered s).sp.toNat + 132 < 2 ^ 32 := by rw [entered_nat s stackFit]; omega_using [argFit]
  have nativeAddr : off (State.addr (entered s).sp) 132 = stackArgAddr s 1 := by
    change State.addr (entered s).sp + BitVec.ofNat 64 132 = _
    rw [← VG.Arm.addr_add nativeRoom, entered_sp]
    have split : BitVec.ofNat 32 132 = BitVec.ofNat 32 128 + BitVec.ofNat 32 4 := rfl
    rw [split, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl
  have incoming : IncomingScratch p (entered s) := by
    refine ⟨by rw [entered_nat s stackFit]; omega_using [argFit], ?_, ?_⟩
    · rw [nativeAddr]; exact entered_read argRead
    · rw [nativeAddr]
      have word := (entered_frame s stackFit).readW (w := 32) contains (by
        intro r hr
        rw [List.mem_singleton] at hr
        subst r
        exact stackArgs.symm.sub_right (saved_sub_reserved s stackFit)) (by decide)
      rw [word]
      exact base
  refine ⟨stackFit, args, incoming, domain, ?_, ?_, publicValue, valueEntered, length, ?_, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [length]
    exact stackY.symm.sub_right (locals_sub_reserved s stackFit)
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm
