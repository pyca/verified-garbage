module

import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
public import VerifiedGarbage.Proof.Weierstrass.Naf5
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigitRead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem nafMagnitude_byte (k j : Nat) : nafMagnitude (Naf5.byte k j)=Naf5.magnitude k j :=
  Naf5.byte_magnitude k j

theorem nafNegative_byte (k j : Nat) : nafNegative (Naf5.byte k j)=Naf5.negative k j :=
  Naf5.byte_negative k j

end VG.Proof.Weierstrass.AArch64
