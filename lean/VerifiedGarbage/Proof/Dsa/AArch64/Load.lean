module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.Omega

/-! # Loading DSA's padded components into a child workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Loading accepts leading zeroes and clears all unused limbs. Computed
operands in the scratch suffix use scratchSource to discharge hsrc. -/
theorem load_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    {j : Nat} (hj : j < 8) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32)
    {p : Addr} {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z p bytes) (hk1 : 1 ≤ bytes.length) (hk' : bytes.length < 2 ^ 31)
    (hkw : (bytes.length + 7) / 8 ≤ wx) :
    WP isa (Arithmetic.load j sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx j) wx = Spec.Dsa.decodeBE bytes ∧
      Outside (off B o) (slot wx j) (8 * (wx + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  rw [decodeBE_os2ip]
  exact primeLoad_ok hc hw2 hwx hw30 hj hsp hsl hp hl hsrc hk1 hk' hkw

end VG.Proof.Dsa.AArch64
