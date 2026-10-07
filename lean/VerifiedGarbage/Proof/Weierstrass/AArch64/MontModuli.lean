import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn

/-!
# Montgomery products as functions on AArch64: the moduli

Each modulus of P-224, P-384 and P-521 is one the functions support (`ModOk`).
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open Spec.Weierstrass.Mont

theorem p224p_ok : ModOk p224p.k p224p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  novec := by decide +kernel

theorem p224n_ok : ModOk p224n.k p224n.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  novec := by decide +kernel

theorem p384p_ok : ModOk p384p.k p384p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  novec := by decide +kernel

theorem p384n_ok : ModOk p384n.k p384n.m where
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

theorem p521n_ok : ModOk p521n.k p521n.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  novec := by decide +kernel

end VG.Proof.Weierstrass.AArch64.Mont
