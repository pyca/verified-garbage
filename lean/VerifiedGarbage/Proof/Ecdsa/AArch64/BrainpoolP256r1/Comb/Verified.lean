module

import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Correct
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi

import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
meta import VerifiedGarbage.Proof.Weierstrass.CombW
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Correct
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-! # brainpoolP256r1 fixed-base signing: correctness, ABI and constant time

The generic signing proof composes the general-curve comb with the existing
input validation, inversions, scalar arithmetic and output masking.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.BrainpoolP256r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem pre_of {s : State} (h : signAArch64.pre s) : Pre combCfg s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds)
    (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signComb s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := signWith_ok (cfg_ok hI) hL comb (correct hL hI) (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signComb :=
  VG.Taint.constantTime (A := taintS [combCfg.tsym]) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds)
    :
    Verified AArch64.target signComb
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP256r1.inst (AArch64.abi.withConsts combCfg.combConsts)) :=
  Verified.of_correct (sign_a64 hL hI) sign_ct implies

end VG.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb
