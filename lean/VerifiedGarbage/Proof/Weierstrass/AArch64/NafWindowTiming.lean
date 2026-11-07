module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinish

import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Framework.RelCTAssoc

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def NafWindowInput (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (k : Nat) (s : State) : Prop :=
  wordsVal s.mem base K.zero K.M.n=0 ∧
  (∀ i<257,s.mem (off base (K.bits+i))=Naf5.byte k i) ∧
  InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y) (tmv C K.M.n base s K.P.z) P

end VG.Proof.Weierstrass.AArch64
