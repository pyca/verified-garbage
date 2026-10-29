module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Input
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Sat
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.RecognitionTiming
import VerifiedGarbage.Impl.Ffdh.Arm.VettedValidation
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Ffdh.Arm.DomainBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Fn
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntry
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.DomainPre
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
/-! Standard-domain recognition and the complete general fallback are verified. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/Correct.lean`, which only this module imported.
section

/-! The fast path and fallback implement the unchanged shared parameter contract. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm

theorem correct (s : State) (pre : contract.pre s) :
    ∃ tr t, Exec isa VG.Impl.Ffdh.Arm.VettedValidation.code s tr t ∧
      abiPreserved s t ∧ contract.post s t := by
  obtain ⟨p, _, domain, count, _, bytes, input⟩ := data s pre
  obtain ⟨tr, t, run, preserved, result⟩ := fn_ok s input
  refine ⟨tr, t, run, preserved, ?_⟩
  change (Spec.Ffdh.checkDomainContract abi 128).post s t
  sig_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right, domain, count]
  change (t.gpr .r0).toNat = if Spec.Ffdh.domainValid p.k
    (Spec.Rsa.bytesAt s.mem (State.addr p.domain) (s.gpr .r1).toNat) then 1 else 0
  rw [bytes, result, checkedDomainFlag_spec]
  split <;> rfl

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/BodyTiming.lean`, which only this module imported.
section

/-! The recognition decision depends only on public domain bytes. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (groups recognize tableSym)

theorem body_ct {p : Inputs} {slots : List Nat}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t =>
      (Context p slots s ∧ VettedGroups.TableAt (s.syms tableSym) groups s) ∧
      (Context p slots t ∧ VettedGroups.TableAt (t.syms tableSym) groups t) ∧
      s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym)
      VG.Impl.Ffdh.Arm.VettedValidation.body (fun _ _ => True) := by
  let P := fun s : State => Context p slots s ∧ VettedGroups.TableAt (s.syms tableSym) groups s
  let Q := fun s : State => Context p slots s ∧
    s.gpr .r11 = BitVec.ofNat 32 (recognize groups p.k p.dom)
  let R := fun s : State => Context p slots s ∧
    s.z = (BitVec.ofNat 32 (recognize groups p.k p.dom) == 0)
  have scan (s : State) (h : P s) : WP isa VG.Impl.Ffdh.Arm.VettedGroups.code s Q :=
    WP.mono (VettedGroups.code_ok s h.1 h24 h28 h32 h.2) fun _ out => ⟨out.1, out.2.1⟩
  have stage := (relCT_keep_sp (VettedGroups.recognition_ct h24 h28 h32)
    (fun _ _ h => h.2.2.1)).wp (fun s t h => ⟨scan s h.1, scan t h.2.1⟩)
  have test (s : State) (h : Q s) : WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s R := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨zero, mem⟩, rest⟩
    exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ptr),
      by rw [zero, h.2]⟩
  have branches : RelCT isa (fun s t => R s ∧ R t ∧ s.sp = t.sp)
      (.ite .ne (VG.Impl.Ffdh.Arm.Domain.ret 1)
        (VG.Impl.Ffdh.Arm.Domain.head VG.Impl.Ffdh.Arm.Domain.CheckDomain.main)) (fun _ _ => True) := by
    apply iteKnown_ct (!(BitVec.ofNat 32 (recognize groups p.k p.dom) == 0))
      (fun s h => by change some (!s.z) = _; rw [h.2])
    · intro _
      exact (ret_ct 1).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · intro _
      exact (domainBody_ct stable h0 h24 h28 h32).mono
        (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)
  have tail := relCT_chain (testFlag_ct.mono (P' := fun (s t : State) => Q s ∧ Q t ∧ s.sp = t.sp)
    (fun _ _ _ => trivial) (fun _ _ h => h)) test test branches
  unfold VG.Impl.Ffdh.Arm.VettedValidation.body
  exact stage.seq (tail.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/FnTiming.lean`, which only this module imported.
section

/-! The frame and recognition introduce no secret-dependent trace. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableSym groups)

theorem fn_ct {p : Inputs} :
    RelCT isa (fun s t => Input p s ∧ Input p t ∧ s.sp = t.sp ∧
      s.syms tableSym = t.syms tableSym)
      VG.Impl.Ffdh.Arm.VettedValidation.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, Input p s ∧ a = entered s
  let Q := fun a : State => Context p [0, 32, 28, 24] a ∧
    VettedGroups.TableAt (a.syms tableSym) groups a
  have wp (a : State) (h : P a) :
      WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) a Q := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono_syms (withAllRest (domainEntry_ok (entered s) input.args
      input.domain input.domainLength input.count input.scratch)) ?_
    rintro u ⟨⟨context, frame⟩, rest⟩ syms
    have table := input.table.after_frame input.safe frame rest
    rw [← syms] at table
    exact ⟨context, table⟩
  have entry : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp ∧
      s.syms tableSym = t.syms tableSym)
      (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry)
      (fun s t => Q s ∧ Q t ∧ s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym) := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := domainEntry_ct s t tr1 tr2 u v h.2.2.1 e1 e2
    obtain ⟨_, u', eu, hu⟩ := wp s h.1
    obtain ⟨_, v', ev, hv⟩ := wp t h.2.1
    obtain ⟨_, rfl⟩ := Exec.det e1 eu
    obtain ⟨_, rfl⟩ := Exec.det e2 ev
    exact ⟨timing.1, hu, hv, by rw [(Exec.rdwr eu).2.2, (Exec.rdwr ev).2.2]; exact h.2.2.1,
      by rw [Exec.syms eu, Exec.syms ev]; exact h.2.2.2⟩
  have body := entry.seq (body_ct (by decide) (by decide) (by decide) (by decide) (by decide))
  unfold VG.Impl.Ffdh.Arm.VettedValidation.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2.1)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2.1], related.2.2.2⟩ e1 e2

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/VettedValidation/Timing.lean`, which only this module imported.
section

/-! Parameter imports reveal only the already-public domain and table addresses. -/

section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem constantTime : ConstantTime isa contract.pre contract.pub
    VG.Impl.Ffdh.Arm.VettedValidation.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, base, domain, count, capacity, domainBytes, inputS⟩ := data s hs
  have relation : (Spec.Ffdh.checkDomainContract abi 128).pub s t ∧
      ∀ c ∈ tableConsts, symAddr s c.1 = symAddr t c.1 := pub_consts.mp hp
  have symbols := VettedGroups.consts_singleton_symEq relation.2
  have pubBase := relation.1
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] at pubBase
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4⟩ := pubBase
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p1] at byteEq
  have preT : (Spec.Ffdh.checkDomainContract abi 128).pre (stripConsts tableConsts t) ∧
      ConstsOk tableConsts 128 t := pre_consts.mp ht
  have inputT := domain_input (stripConsts tableConsts t) preT.1 (p := p)
    (p3.symm.trans base) (p0.symm.trans domain)
    (by change (t.gpr .r2).toNat = p.k; rw [← p2]; exact count)
    (by change (stackArg t 0).toNat = p.len; rw [← p4]; exact capacity) ?_
  · have wide := input_widen inputT
    have table := table_input preT.2 wide
    exact (fn_ct s t tr1 tr2 u v ⟨inputS, ⟨wide, table.1, table.2⟩, sp, symbols⟩ e1 e2).1
  · change Spec.Rsa.bytesAt t.mem (State.addr p.domain) (t.gpr .r1).toNat = p.dom
    rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← byteEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm.VettedValidation
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedValidation
open VG VG.Arm

theorem verified : Verified target VG.Impl.Ffdh.Arm.VettedValidation.code contract :=
  ⟨correct, constantTime, sat⟩

end VG.Proof.Ffdh.Arm.VettedValidation
