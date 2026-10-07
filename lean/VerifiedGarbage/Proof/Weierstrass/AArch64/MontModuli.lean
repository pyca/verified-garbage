import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn

/-!
# Montgomery products as functions on AArch64: the moduli

The prime `p` of P-384 and of P-521 is one the functions support (`ModOk`).
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open Spec.Weierstrass.Mont

theorem p384p_ok : ModOk p384p.k p384p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  novec := by decide +kernel

theorem p521p_ok : ModOk p521p.k p521p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  novec := by decide +kernel

end VG.Proof.Weierstrass.AArch64.Mont
