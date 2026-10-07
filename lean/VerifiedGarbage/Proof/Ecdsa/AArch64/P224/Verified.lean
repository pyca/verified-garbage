import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Lit
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.P224.Prime

/-!
# ECDSA over P-224 on AArch64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P224.law` and `invSound_of_toM`), so `sign_ok` gives
the contract's postcondition; `x19`–`x25` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

namespace VG.Proof.Ecdsa.AArch64.P224

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p224_nBits : Spec.Ecdsa.nBits p224.C = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h1 : 223 ≤ Spec.P224.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P224.curve.n.log2 < 224 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `28` bytes is dropped. -/
theorem p224_sh : p224.sh = 0 := by
  unfold Cfg.sh
  rw [p224_nBits]
  rfl

theorem p224_ok (hI : Weierstrass.AArch64.InvSounds) : CfgOk p224 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P224.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  n2 := by decide
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [p224_sh]; decide
  n4 := by decide
  sound_p := hI (by
    show Nat.Prime Spec.P224.curve.p
    rw [show Spec.P224.curve.p =
      26959946667150639794667015087019630673557916260026308143510066298881
      by decide +kernel]
    exact Proof.P224.prime_26959946667150639794667015087019630673557916260026308143510066298881)
  inv_p := InvOk.ofMod (by decide +kernel) (by decide)
  inv_n := fun _ => ⟨hI Proof.P224.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  chain_n := fun h => absurd h (by decide)
  am3 := by unfold AM3; decide +kernel

theorem pre_of {s : State} (h : signAArch64.pre s) : Pre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signP224 s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-224's
  -- terms before the literals' facts are known.
  have hn : signP224.noCalls = true := by lit_decide
  have hu : KeepsUntouched signP224 := by lit_decide
  have hv : signP224.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p224_ok hI) hL hT (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signP224 :=
  VG.Taint.constantTime (A := taintS [p224.tsym]) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) :
    Verified AArch64.target signP224
      (Spec.Ecdsa.P224.inst.signContract (AArch64.abi.withConsts p224.combConsts)) :=
  Verified.of_correct (sign_a64 hL hI hT) sign_ct implies

end VG.Proof.Ecdsa.AArch64.P224
