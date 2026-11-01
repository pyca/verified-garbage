module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn

/-!
# Montgomery arithmetic as functions on PPC64LE: the moduli

Each modulus of `Impl.Weierstrass.Mont.moduli` is one the functions support
(`ModOk`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open Impl.Weierstrass.Mont

theorem p192p_ok : ModOk p192p.k p192p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p192n_ok : ModOk p192n.k p192n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p224p_ok : ModOk p224p.k p224p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p224n_ok : ModOk p224n.k p224n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p256p_ok : ModOk p256p.k p256p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p256n_ok : ModOk p256n.k p256n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p384p_ok : ModOk p384p.k p384p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p384n_ok : ModOk p384n.k p384n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p521p_ok : ModOk p521p.k p521p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem p521n_ok : ModOk p521n.k p521n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem secp256k1p_ok : ModOk secp256k1p.k secp256k1p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem secp256k1n_ok : ModOk secp256k1n.k secp256k1n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem brainpoolp256r1p_ok : ModOk brainpoolp256r1p.k brainpoolp256r1p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem brainpoolp256r1n_ok : ModOk brainpoolp256r1n.k brainpoolp256r1n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem brainpoolp384r1p_ok : ModOk brainpoolp384r1p.k brainpoolp384r1p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem brainpoolp384r1n_ok : ModOk brainpoolp384r1n.k brainpoolp384r1n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem brainpoolp512r1p_ok : ModOk brainpoolp512r1p.k brainpoolp512r1p.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

theorem brainpoolp512r1n_ok : ModOk brainpoolp512r1n.k brainpoolp512r1n.m where
  n1 := by decide
  n9 := by decide
  m0 := by decide +kernel
  m_lt := by decide +kernel
  inv := by decide +kernel

end VG.Proof.Weierstrass.PPC64LE.Mont
