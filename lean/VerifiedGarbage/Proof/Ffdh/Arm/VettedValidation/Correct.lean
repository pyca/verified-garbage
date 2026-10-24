module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedValidation.Input
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! The fast path and fallback implement the unchanged shared parameter contract. -/

@[expose] public section
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
