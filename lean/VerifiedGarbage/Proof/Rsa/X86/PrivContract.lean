module
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Rsa.X86.PrivObservations
import VerifiedGarbage.Proof.Rsa.X86.PrivFn
import VerifiedGarbage.Proof.Rsa.X86.PrivFnTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivContractInput

/-! # Checked private RSA implements the shared contract and permitted leakage -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86

theorem private_contract_correct (v : CrtImpl) (s : State) (h : (Spec.Rsa.privateCheckedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa (privCode v) s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.privateCheckedContract abi stackBytes).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := privateFn_ok v s (private_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem private_contract_ct (v : CrtImpl) : ConstantTime isa (Spec.Rsa.privateCheckedContract abi stackBytes).pre
    (Spec.Rsa.privateCheckedContract abi stackBytes).pub (privCode v) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := private_contract_pre s hs
  have it := private_contract_pre t ht
  obtain ⟨nb, eb⟩ := publicBytes hp
  rw [← publicGeometry hp] at it
  exact (privateFn_relCT v nb eb s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1
end VG.Proof.Rsa.X86.PrivChecked
