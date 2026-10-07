import VerifiedGarbage.Proof.Weierstrass.Arm.MontFn

/-!
# Montgomery arithmetic as functions on 32-bit ARM: the moduli

Each modulus of `Spec.Weierstrass.Mont.moduli` is one the functions support
(`ModOk`).
-/

namespace VG.Proof.Weierstrass.Arm.Mont

open Spec.Weierstrass.Mont

theorem p224p_ok : ModOk p224p.k p224p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p224n_ok : ModOk p224n.k p224n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p256p_ok : ModOk p256p.k p256p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p256n_ok : ModOk p256n.k p256n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p384p_ok : ModOk p384p.k p384p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p384n_ok : ModOk p384n.k p384n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p521p_ok : ModOk p521p.k p521p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p521n_ok : ModOk p521n.k p521n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

end VG.Proof.Weierstrass.Arm.Mont
