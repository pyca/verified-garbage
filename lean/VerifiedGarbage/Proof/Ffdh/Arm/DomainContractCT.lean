module

public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Ffdh.Arm.DomainCorrect
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.Arm.DomainPre
import VerifiedGarbage.Proof.Ffdh.Arm.DomainFn
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntryCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainBodyCT
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Ffdh.Arm.Entered
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Ffdh.Arm.DomainEntry
/-! The native parameter checker satisfies the shared timing policy. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/DomainFnCT.lean`, which only this module imported.
section

/-! The callable domain check reveals only the public domain. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem domainFn_ct {p : Inputs} :
    RelCT isa (fun s t => DomainFnInput p s ∧ DomainFnInput p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.Domain.CheckDomain.code (fun _ _ => True) := by
  let P := fun a : State => ∃ s, DomainFnInput p s ∧ a = entered s
  have entry := domainEntry_ct.mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (a : State) (h : P a) : WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) a
      (Context p [0, 32, 28, 24]) := by
    obtain ⟨s, input, rfl⟩ := h
    refine WP.mono (withAllRest (domainEntry_ok (entered s) input.args
      input.domain input.domainLength input.count input.scratch)) ?_
    rintro u ⟨⟨context, _⟩, _⟩
    exact context
  have body := relCT_chain entry wp wp
    (domainBody_ct (by decide) (by decide) (by decide) (by decide) (by decide))
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.code
  apply framed_ct (fun _ _ h => ⟨h.1.stackFits, h.2.1.stackFits⟩) (fun _ _ h => h.2.2)
  intro a b tr1 tr2 u v h e1 e2
  obtain ⟨s, t, related, rfl, rfl⟩ := h
  exact body _ _ _ _ _ _ ⟨⟨s, related.1, rfl⟩, ⟨t, related.2.1, rfl⟩,
    by rw [entered_sp, entered_sp, related.2.2]⟩ e1 e2

end VG.Proof.Ffdh.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem domain_contract_ct : ConstantTime isa (Spec.Ffdh.checkDomainContract abi 128).pre
    (Spec.Ffdh.checkDomainContract abi 128).pub VG.Impl.Ffdh.Arm.Domain.CheckDomain.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, base, domain, count, capacity, domainBytes, inputS⟩ := domain_data s hs
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, List.map_id'] at byteEq
  rw [← p0, ← p1] at byteEq
  have inputT := domain_input t ht (p := p) (p3.symm.trans base) (p0.symm.trans domain)
    (by rw [← p2]; exact count) (by rw [← p4]; exact capacity) ?_
  · exact (domainFn_ct s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p1, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat = p.dom
    rw [← byteEq, domain]
    exact domainBytes

end VG.Proof.Ffdh.Arm
