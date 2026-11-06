module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Impl.Ecdh.AArch64.WithMul
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

@[expose] public section

namespace VG.Proof.Ecdh.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)
variable {c : Cfg}

/-- The established inputs to an arbitrary scalar multiplication. -/
def MulInput (c : Cfg) (s : State) : Prop :=
  ∃ (base : Addr) (g : Reg → BitVec 64) (P : Point c.C),
    Scr s base size ∧ Fixed c base g s.mem ∧ onCurve c.C P = true ∧
    sv c base s PX < c.C.p ∧ sv c base s PY < c.C.p ∧
    Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P

end VG.Proof.Ecdh.AArch64
