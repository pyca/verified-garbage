module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontOpArgs
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-! # The header kept by the generator-two exponent loop

`header_of_keeps`: an action that keeps the arithmetic layout keeps the
header (`HeaderKept`).
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem header_of_keeps {base : BitVec 32} {len w o : Nat} {s t : State}
    (ready : ArithmeticReady base len w s) (keeps : Keeps (State.addr base) len w o s.mem t.mem) :
    HeaderKept base s t := by
  have fit : arrAt w 8 ≤ 8 * len := ready.width ▸ ready.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fit; omega
  intro d hd
  exact keeps_header_readW keeps size (d := d) (bits := 32) (by omega)

end VG.Proof.Bignum.Arm.TwoExp
