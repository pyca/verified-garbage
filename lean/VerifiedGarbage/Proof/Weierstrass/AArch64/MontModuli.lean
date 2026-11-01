module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG

/-!
# Montgomery products as functions on AArch64: the moduli

The prime `p` of P-384 and of P-521, and P-384's and P-521's orders `n`, are moduli the
functions support (`ModOk`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Mont

open Impl.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont

theorem p384p_okS : ModOkS p384p.k p384p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  kind := .inl ⟨by decide +kernel, by decide +kernel⟩
  x6 := by decide +kernel
  loads := by decide +kernel
  lnd := by decide +kernel
  novec := by decide +kernel

theorem p521p_okS : ModOkS p521p.k p521p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  kind := .inr ⟨by decide +kernel, friendly_of (by decide +kernel)⟩
  x6 := by decide +kernel
  loads := by decide +kernel
  lnd := by decide +kernel
  novec := by decide +kernel

theorem p384p_fn : mulFn p384p.k p384p.m = mulFn384 := by
  simp only [mulFn, show Impl.Mont.sparseOk p384p.k p384p.m = true by decide +kernel, ↓reduceIte]
theorem p521p_fn : mulFn p521p.k p521p.m = mulFnS p521p.k p521p.m := by
  simp only [mulFn, show Impl.Mont.sparseOk p521p.k p521p.m = false by decide +kernel, p521p_okS.general,
    Bool.false_eq_true, ↓reduceIte]

theorem p384p_ok : ModOk p384p.k p384p.m := .inl p384p_okS
theorem p521p_ok : ModOk p521p.k p521p.m := .inl p521p_okS

theorem p521n_ok : ModOk p521n.k p521n.m := .inr {
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  g := by decide +kernel
  novec := by decide +kernel }

theorem p384n_ok : ModOk p384n.k p384n.m := .inr {
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  g := by decide +kernel
  novec := by decide +kernel }

theorem p384n_fn : mulFn p384n.k p384n.m = mulFnG p384n.k p384n.m := by
  rcases p384n_ok with h | h
  · exact absurd h.general (by decide +kernel)
  · simp only [mulFn, sparseOk_of_general h.g, h.g, Bool.false_eq_true, ↓reduceIte]

theorem p521n_fn : mulFn p521n.k p521n.m = mulFnG p521n.k p521n.m := by
  rcases p521n_ok with h | h
  · exact absurd h.general (by decide +kernel)
  · simp only [mulFn, sparseOk_of_general h.g, h.g, Bool.false_eq_true, ↓reduceIte]

end VG.Proof.Weierstrass.AArch64.Mont
