module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointAbi
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find

/-! The joint P-521 verifier satisfies the existing public verification contract.
The width-seven generator and width-five peer digits share one doubling chain;
all branch decisions depend only on the contract's public signature inputs. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521

theorem pre_of {s : State} (h : verifyAArch64.pre s) : VPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem verify_a64 (hL : Weierstrass.Law Spec.P521.curve) (hO : Weierstrass.PrimeOrder Spec.P521.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (s : State)
    (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP521 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := Joint.verify_ok (p521_ok hI) hL hO (by decide) hT
    (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_callsKeep verify_untouched verify_keepsV hsv, hpost⟩

/-- The contract's public inputs: the pointers, the table, and the key, digest and signature. -/
theorem jacPublic_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P521.inst.verifyContract (AArch64.abi.withConsts p521.combConsts)).pub s₁ s₂) :
    JacPublic p521 s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p521_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp, hsy, inputs, h0, h1, h2, h3⟩ := pub
  refine ⟨⟨hsp, fun r hr => ?_⟩, hsy, ?_, ?_, ?_⟩
  · simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append, Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.1
  · exact front.2
  · exact parts.2

end VG.Proof.Ecdsa.Verify.AArch64.P521
