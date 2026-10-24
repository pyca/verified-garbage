module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyImplies
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_dsa_verify_prevalidated` on PPC64LE: the contract on the registers and the stack

`prevalidated_implies`: `vpContract` implies the shared contract. The
witness is `vg_dsa_verify`'s (`satState`) with a key that passes validation
(`validKeyWitness`) at `0x1000`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `satState` with `validKeyWitness` at `0x1000`. -/
def prevalidatedSatState : State where
  gpr := satState.gpr
  lr := satState.lr
  sp := satState.sp
  mem a := if 0x1000 ≤ a.toNat ∧ a.toNat < 0x1194 then
    VG.Proof.Dsa.validKeyWitness[a.toNat - 0x1000]?.getD 0 else satState.mem a
  rd := satState.rd
  wr := satState.wr

theorem prevalidatedSat_key :
    Spec.Rsa.bytesAt prevalidatedSatState.mem 0x1000 404 = VG.Proof.Dsa.validKeyWitness := by
  decide +kernel

theorem prevalidated_implies : vpContract.Implies (Spec.Dsa.verifyPrevalidatedContract abi) where
  pre := by
    sig_implies_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, vpContract,
      vContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two]
  post := by
    sig_implies_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, vpContract,
      vContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two]
  pub := by
    sig_implies_pub [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, vpContract,
      vContract, stackArgs_two, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two]
  sat := by
    have hv : Spec.Dsa.validatePublicKeyBytes 128 20
        (Spec.Rsa.bytesAt prevalidatedSatState.mem 0x1000 404) = true := by
      rw [prevalidatedSat_key]; exact VG.Proof.Dsa.validKeyWitness_valid
    refine ⟨prevalidatedSatState, ?_⟩
    sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_two,
      List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
      List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
      List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, pairFacts_two]
    sig_and_intros
    trace_state
    all_goals sorry

end VG.Proof.Dsa.PPC64LE
