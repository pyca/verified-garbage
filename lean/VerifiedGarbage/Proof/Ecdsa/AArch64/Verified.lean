import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi

/-!
# ECDSA over P-256 on AArch64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P256.law`), so `sign_ok` gives
the contract's postcondition; `x19` and `x20` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p256_nBits : 64 * p256.n ≤ Spec.Ecdsa.nBits p256.C := by
  show 256 ≤ Spec.P256.curve.n.log2 + 1
  have : 255 ≤ Spec.P256.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

theorem p256_ok : CfgOk p256 where
  n0 := by decide
  n7 := by decide
  onG := Proof.P256.onCurve_G
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
  tbl_len := by decide
  len := rfl
  hash := p256_nBits

theorem pre_of {s : State} (h : signAArch64.pre s) : Pre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem sign_a64 (hL : Weierstrass.Law Spec.P256.curve)
    (hT : CombOk Spec.P256.curve 64 Impl.P256.p256Comb Impl.P256.p256CombStart) (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa signP256 s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok p256_ok hL hT (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, hpost⟩

theorem sign_ct : ConstantTime isa signAArch64.pre signAArch64.pub signP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

theorem sign_verified (hL : Weierstrass.Law Spec.P256.curve)
    (hT : CombOk Spec.P256.curve 64 Impl.P256.p256Comb Impl.P256.p256CombStart) :
    Verified AArch64.target signP256 (Spec.Ecdsa.P256.inst.signContract AArch64.abi) :=
  Verified.of_correct (sign_a64 hL hT) sign_ct implies

end VG.Proof.Ecdsa.AArch64
