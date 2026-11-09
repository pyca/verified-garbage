module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG

/-! # Shared BrainpoolP384r1 Montgomery multiplication on AArch64 -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.Mont
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont Impl.Weierstrass.Mont

theorem brainpoolp384r1p_ok : ModOk brainpoolp384r1p.k brainpoolp384r1p.m := .inr {
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  g := by decide +kernel
  novec := by decide +kernel }

theorem brainpoolp384r1n_ok : ModOk brainpoolp384r1n.k brainpoolp384r1n.m := .inr {
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  g := by decide +kernel
  novec := by decide +kernel }

end VG.Proof.Weierstrass.AArch64.Mont
