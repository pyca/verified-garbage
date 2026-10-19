module

public import VerifiedGarbage.Impl.P256.Booth
meta import VerifiedGarbage.Impl.P256.Booth
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
meta import VerifiedGarbage.Proof.EcKey.AArch64.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
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
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
meta import VerifiedGarbage.Proof.Weierstrass.JacMul
meta import VerifiedGarbage.Spec.Weierstrass.Mul

/-! The comb that signing and public keys share is checked once, and their
literals read it.

The comb's forwarded field programs (`CombArithmetic.program`) are the
optimizer's output, which `Forward.CombMixed` and `Forward.CombOut` already
have as literals: the comb's literal is its code with those, by rewriting,
rather than the kernel running the optimizer again. -/

@[expose] public section

namespace VG.Impl.P256.Booth
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

private theorem program_eq (k : CombArithmetic.Kind) :
    CombArithmetic.program CombArithmetic.K.M (CombArithmetic.operations k) =
      .block (VG.Proof.Weierstrass.AArch64.Forward.CombArithmetic.optimized k) := by
  rw [CombArithmetic.program,
    ite_eq_left ⟨rfl, List.mem_map.mpr ⟨k, by cases k <;> decide, rfl⟩⟩]
  rfl

private theorem mixed_eq : CombArithmetic.program CombArithmetic.K.M
    (maddJ CombArithmetic.K.S CombArithmetic.K.A CombArithmetic.K.E CombArithmetic.K.D) =
    .block VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit :=
  (program_eq .mixed).trans
    (congrArg Code.block VG.Proof.Weierstrass.AArch64.Forward.CombMixed.optimized_lit)

private theorem out_eq : CombArithmetic.program CombArithmetic.K.M CombArithmetic.K.outOps =
    .block VG.Proof.Weierstrass.AArch64.Forward.CombOut.rightCode.lit :=
  (program_eq .out).trans
    (congrArg Code.block VG.Proof.Weierstrass.AArch64.Forward.CombOut.optimized_lit)

/-- `comb`, with the literals of its field programs. -/
noncomputable def comb.lit : Prog isa :=
  .seq CombArithmetic.K.first <|
  .seq (.loop
    (.seq (.block (CombArithmetic.K.bdigit true ++ CombArithmetic.K.select)) <|
      .seq (.block CombArithmetic.K.bnegY) <|
      .seq (.block VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit) <|
      .seq (.block (nzMask CombArithmetic.K.M.n CombArithmetic.K.A.z ++
        selPt CombArithmetic.K.M.n CombArithmetic.K.D CombArithmetic.K.E CombArithmetic.K.D)) <|
      .block (CombArithmetic.K.bdigit true ++ [Mont.AArch64.zero7, .movz .x .x5 1 0, .subs .x .x16 .x2 .x5,
        .sbc .x .x3 .x7 .x7] ++ selPt CombArithmetic.K.M.n CombArithmetic.K.A CombArithmetic.K.D
          CombArithmetic.K.A ++
        [.addImm .x .x19 .x19 1, .subImm .x .x4 .x19 CombArithmetic.K.J]))
    (.nonzero .x .x4)) <|
  .seq (.block CombArithmetic.K.outFix) (.block VG.Proof.Weierstrass.AArch64.Forward.CombOut.rightCode.lit)

theorem comb.lit_eq : comb = comb.lit := by
  simp only [comb, TCombCfg.combJWith, TCombCfg.stepJWith]
  rw [mixed_eq, out_eq]
  rfl

materialize_code sign
materialize_code publicKey

end VG.Impl.P256.Booth
