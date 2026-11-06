module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeInvariant

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowCore
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

/-! The full public Jacobian variable-point multiplication. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

def jacWindowClob (K : WinCfg) : List Reg := .x20 :: tcombClob K.M.n

end VG.Proof.Weierstrass.AArch64
