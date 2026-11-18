module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainFn
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
import VerifiedGarbage.Proof.Ffdh.Arm.Branch

/-! ### `Ffdh.Arm.VettedValidation.Fn`, which the modules that import this one used -/

section

/-! The recognized-domain checker uses the existing 128-byte AAPCS frame. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/Body.lean`, which only this module imported.
section

/-! Exact recognition proves the existing domain-validity predicate. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups recognize)

theorem body_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s) :
    WP isa VG.Impl.Ffdh.Arm.VettedValidation.body s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.VettedValidation.body, WP.seq_iff]
  refine WP.mono (VettedGroups.code_ok s h h24 h28 h32 table) ?_
  rintro u ⟨context, cap, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (VettedGroups.zero_test u .r11) ?_
  rintro v ⟨⟨zero, memV⟩, restV⟩
  have value : v.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0) := by
    rw [zero, cap]
  by_cases hit : BitVec.ofNat 32 (recognize groups p.k p.dom) ≠ 0
  · refine WP.ite true (by simp only [eval, value, beq_eq_false_iff_ne.mpr hit]; rfl)
      (fun _ => ?_) (fun bad => Bool.noConfusion bad)
    have recognized : recognize groups p.k p.dom ≠ 0 := by
      intro impossible
      exact hit (by rw [impossible]; rfl)
    have valid := VG.Proof.Ffdh.VettedValidation.recognized_domain_valid groups
      (fun _ hg => hg) (by rw [p.domainLength]; split <;> simp) recognized
    refine WP.mono (ret_ok v 1 (by decide)) ?_
    rintro t ⟨⟨result, memT⟩, _⟩
    refine ⟨?_, ?_⟩
    · rw [checkedDomainFlag_spec, valid]
      exact result
    · rw [memT, memV, memU]
      exact Frame.refl _ _
  · have contextV := context.of_mem memV restV ((restV.gpr .r0 (by simp)).trans context.ptr)
    refine WP.ite false (by rw [Classical.not_not] at hit; simp only [eval, value, hit]; rfl)
      (fun bad => Bool.noConfusion bad) (fun _ => ?_)
    refine WP.mono (domainBody_ok v contextV stable h0 h24 h28 h32) ?_
    rintro t ⟨result, frame⟩
    refine ⟨result, ?_⟩
    rw [memV, memU] at frame
    simpa only [bodyWrites, restV.sp, restU.sp] using frame

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups)

structure Input (p : Inputs) (s : State) : Prop extends DomainFnInput p s where
  table : VettedGroups.TableAt ((entered s).syms tableSym) groups (entered s)
  safe : VettedGroups.TableSafe ((entered s).syms tableSym) groups
    [⟨State.addr (entered s).sp, 72⟩]

theorem entered_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (scratch : s.gpr .r3 = p.base)
    (table : VettedGroups.TableAt (s.syms tableSym) groups s)
    (safe : VettedGroups.TableSafe (s.syms tableSym) groups [⟨State.addr s.sp, 72⟩]) :
    WP isa (.seq (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      VG.Impl.Ffdh.Arm.VettedValidation.body) s fun t =>
      t.gpr .r0 = checkedDomainFlag p ∧ Frame (bodyWrites p s) s.mem t.mem := by
  rw [WP.seq_iff]
  refine WP.mono_syms (withAllRest (domainEntry_ok s h domain domainLength count scratch)) ?_
  rintro u ⟨⟨context, frameU⟩, restU⟩ syms
  have tableU := table.after_frame safe frameU restU
  rw [← syms] at tableU
  refine WP.mono (body_ok u context (by decide) (by decide) (by decide)
    (by decide) (by decide) tableU) ?_
  rintro t ⟨result, frameT⟩
  have entryFrame : Frame (bodyWrites p s) s.mem u.mem := frameU.mono (by simp [bodyWrites])
  change Frame [⟨State.addr p.base, 8 * p.len⟩, ⟨State.addr u.sp, 72⟩] u.mem t.mem at frameT
  rw [restU.sp] at frameT
  exact ⟨result, entryFrame.trans frameT⟩

theorem fn_ok (s : State) {p : Inputs} (h : Input p s) :
    WP isa VG.Impl.Ffdh.Arm.VettedValidation.code s fun t =>
      abiPreserved s t ∧ t.gpr .r0 = checkedDomainFlag p := by
  unfold VG.Impl.Ffdh.Arm.VettedValidation.code
  refine framed_of_separate _ s h.stackFits (bodyWrites p (entered s))
    (fun _ status => status = checkedDomainFlag p) h.saved ?_
  refine WP.mono (entered_ok (entered s) h.args h.domain h.domainLength
    h.count h.scratch h.table h.safe) ?_
  rintro t ⟨result, frame⟩
  exact ⟨frame, result⟩

end VG.Proof.Ffdh.Arm.VettedValidation

end

end

/-! ### `Ffdh.Arm.DomainPre`, which the modules that import this one used -/

section

/-! The shared domain signature supplies the complete native frame and buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem domain_input (s : State) (pre : (Spec.Ffdh.checkDomainContract abi 128).pre s)
    {p : Inputs} (base : s.gpr .r3 = p.base) (domain : s.gpr .r0 = p.domain)
    (count : (s.gpr .r2).toNat = p.k) (capacity : (stackArg s 0).toNat = p.len)
    (domainBytes : Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat = p.dom) :
    DomainFnInput p s := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, _, rd, wr, domS, _, stackDom, stackS, _, domFit, sFit, _, _, _⟩ := pre
  have domLen : (s.gpr .r1).toNat = p.dom.length := by
    have eq := congrArg List.length domainBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq
  rw [domain, domLen] at rd domS stackDom domFit
  rw [base, capacity, Nat.mul_comm p.len 8] at wr domS stackS sFit
  have reserved : State.addr s.sp - BitVec.ofNat 64 128 = State.addr (s.sp - BitVec.ofNat 32 128) :=
    (FrameStack.addr_sub' stackFit).symm
  simp only [State.addr] at reserved
  rw [reserved] at stackDom stackS
  have ws : Workspace s p.base (8 * p.len) := ⟨sFit, by rw [wr]; simp [State.addr]⟩
  have domRead : InRegions (s.rd ++ s.wr) (State.addr p.domain) p.dom.length :=
    ⟨⟨State.addr p.domain, p.dom.length⟩, List.mem_append_left _ (by rw [rd]; simp [State.addr]), Region.contains_self _ _⟩
  have domOctets : Octets p.base p.domain p.len p.dom s :=
    ⟨domFit, domRead, domS, by rw [← domLen]; exact domainBytes⟩
  have args : ArgumentMemory p [] (entered s) :=
    ⟨entered_workspace ws, entered_locals s stackFit stackS, entered_octets domOctets stackFit stackDom,
      stackDom.symm.sub_right (locals_sub_reserved s stackFit), by simp⟩
  refine ⟨stackFit, args, domain, ?_, ?_, base, ?_⟩
  · rw [← domLen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackS.sub_left (saved_sub_reserved s stackFit)
    · exact saved_separate_locals s stackFit

end VG.Proof.Ffdh.Arm

end

end

/-! A verified native FFDH backend, for domain/key validation and exchange. Callers inherit every implementation's feature requirements. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure Backend where
  checkDomain : Prog isa
  checkDomain_verified : Verified target checkDomain (Spec.Ffdh.checkDomainContract (abi.withConsts VG.Impl.Ffdh.Arm.VettedGroups.tableConsts) 128)
  checkPublic : Prog isa
  checkPublic_verified : Verified target checkPublic (Spec.Ffdh.checkPublicContract abi 128)
  checkPrivate : Prog isa
  checkPrivate_verified : Verified target checkPrivate (Spec.Ffdh.checkPrivateContract abi 128)
  exchange : Prog isa
  exchange_verified : Verified target exchange (Spec.Ffdh.exchangeContract abi 128)
  suffix : String
  features : List String

end VG.Proof.Ffdh.Arm
