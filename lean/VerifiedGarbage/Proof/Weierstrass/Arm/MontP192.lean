module

public import VerifiedGarbage.Proof.Weierstrass.Arm.MontFn
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public meta import VerifiedGarbage.Proof.Weierstrass.Arm.MontFn

/-!
# Montgomery arithmetic modulo P-192's `p` and `n`, as functions, on 32-bit ARM: verified

P-192's moduli, in three 64-bit words, are ones the functions support
(`ModOk`), so each of their functions meets the contract of its `Api`, as
the other curves' do (`MontVerified.lean`). Apart from the other curves', so
that adding them rebuilds none of their proofs.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Impl.Weierstrass.Mont

theorem p192p_ok : ModOk p192p.k p192p.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

theorem p192n_ok : ModOk p192n.k p192n.m where
  n3 := by decide
  n9 := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel

end VG.Proof.Weierstrass.Arm.Mont
