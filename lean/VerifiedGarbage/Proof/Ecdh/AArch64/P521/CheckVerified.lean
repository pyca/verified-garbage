module

public import VerifiedGarbage.Proof.Ecdh.AArch64.CheckPoint
meta import VerifiedGarbage.Proof.Ecdh.AArch64.CheckPoint
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.P521.AArch64
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
meta import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# `vg_p521_check_point` on AArch64: `Verified`

`check_correct` (`Proof/Ecdh/AArch64/CheckPoint.lean`) for P-521's configuration, constant
time by taint tracking (`x0` and `sp` public), and a state satisfying the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P521.Check

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Ecdh.AArch64.CheckPoint
open VG.Proof.Ecdsa.AArch64.P521

/-- P-521's curve of `Spec/Weierstrass/CheckPoint.lean`. -/
abbrev C : Spec.Weierstrass.CheckPoint.Curve := Spec.Weierstrass.CheckPoint.p521

/-- By the kernel, which evaluates the primes. -/
theorem check_curve : Impl.Ecdh.AArch64.Cfg.checkCurve p521 = some C := by
  unfold Impl.Ecdh.AArch64.Cfg.checkCurve Spec.Weierstrass.CheckPoint.curves
  rw [List.find?_cons_of_neg (by decide +kernel)]
  rw [List.find?_cons_of_neg (by decide +kernel)]
  rw [List.find?_cons_of_neg (by decide +kernel)]
  rw [List.find?_cons_of_neg (by decide +kernel)]
  rw [List.find?_cons_of_neg (by decide +kernel)]
  exact List.find?_cons_of_pos (by decide +kernel)

theorem correct (hI : Proof.Weierstrass.AArch64.InvSounds) (s : State) (hs : (ptK C).pre s) :
    ∃ t s', Exec isa (Impl.Ecdh.AArch64.Cfg.checkFn p521) s t s' ∧ abiPreserved s s' ∧ (ptK C).post s s' :=
  check_correct ((p521_ok hI).toBaseCfgOk) check_curve rfl rfl s hs

/-- Constant time by taint tracking, `x0` and `sp` public. -/
theorem ct : ConstantTime isa (ptK C).pre (ptK C).pub (Impl.Ecdh.AArch64.Cfg.checkFn p521) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) (agree C) (by taint_decide)

theorem sat : C.pre 0x1000 (satMem C) := by
  unfold Spec.Weierstrass.CheckPoint.Curve.pre
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, .inl (by decide +kernel)⟩

/-- `vg_p521_check_point` on AArch64. -/
theorem verified (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target (Impl.Ecdh.AArch64.Cfg.checkFn p521) (C.checkContract AArch64.abi) :=
  Verified.of_correct (correct hI) ct (check_implies C sat)

end VG.Proof.Ecdh.AArch64.P521.Check
