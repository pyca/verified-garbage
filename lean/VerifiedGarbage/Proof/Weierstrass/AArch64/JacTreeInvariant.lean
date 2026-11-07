module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def jacTreeSlots (K : WinCfg) (m : Nat) : List Nat :=
  (List.range (3*m)).map fun i => K.tbl+32*i

end VG.Proof.Weierstrass.AArch64
