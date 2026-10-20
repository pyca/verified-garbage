module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupWs

/-!
# RSA with the CRT on AArch64: constant time of the primes' setup

`WindowFive.primesSetup` is the code of `Crt.primesSetup`, and its
precondition is `SetupPre`'s (`offQ32` is `offQ`, `tabBytes32` is `wsTab`):
`setup_ct` is the 4-bit setup's.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive

def SetupPre (p : SetupPub) (s : State) : Prop :=
  ∃ pb qb ib : List Byte, Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ32 p.w p.pl + slot (wsWords p.ql) 8 + tabBytes32 (wsWords p.ql) ≤ p.Z ∧
    word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    word s.mem p.B (8 * sP) = p.pp ∧ word s.mem p.B (8 * sQ) = p.qp ∧ word s.mem p.B (8 * sQinv) = p.ip ∧
    Src s p.B p.Z p.pp pb ∧ Src s p.B p.Z p.qp qb ∧ Src s p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

/-- `primesSetup` is constant time. -/
def SetupCT : Prop := RelCT isa (Two SetupPre) (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) fun _ _ => True

theorem setup_ct : SetupCT := VG.Proof.Bignum.AArch64.setup_ct

end VG.Proof.Bignum.AArch64.WindowFive
