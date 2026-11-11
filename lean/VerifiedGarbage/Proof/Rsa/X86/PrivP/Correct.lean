module
public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Fn
public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Contract
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # `vg_rsa_private_checked_precomputed` on x86: correct -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86

theorem private_contractP_correct (v : CrtImpl) (w : CrtPImpl) (s : State)
    (h : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa (privCodeP v w) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).post s t := by
  obtain ⟨I, H⟩ := private_contractP_pre h
  obtain ⟨tr, t, run, preserved, post⟩ := privateFnP_ok v w s I H
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact post
end VG.Proof.Rsa.X86.PrivChecked
