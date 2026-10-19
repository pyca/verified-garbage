module

import VerifiedGarbage.Proof.X448.AArch64.Fast.Main
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Main
import VerifiedGarbage.Proof.X448.AArch64.Fast.Lit
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
public import VerifiedGarbage.Proof.X448.AArch64.Main
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Curve448.AArch64.AccumSquareBody
import VerifiedGarbage.Proof.Curve448.AArch64.AddEval
import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
import VerifiedGarbage.Proof.Curve448.AArch64.Collect
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Butterfly
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.ColEnd
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Arith
import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
import VerifiedGarbage.Proof.Curve448.AArch64.Product
import VerifiedGarbage.Proof.Curve448.AArch64.Stage
import VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumn
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.AArch64.AddSub
import VerifiedGarbage.Proof.X448.AArch64.BitStep
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.X448.AArch64.Bits
import VerifiedGarbage.Proof.X448.AArch64.Carry
import VerifiedGarbage.Proof.X448.AArch64.Columns
import VerifiedGarbage.Proof.X448.AArch64.Copy
import VerifiedGarbage.Proof.X448.AArch64.Decode
import VerifiedGarbage.Proof.X448.AArch64.DecodeAll
import VerifiedGarbage.Proof.X448.AArch64.DecodeStore
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.AArch64.Initial
import VerifiedGarbage.Proof.X448.AArch64.Inv
import VerifiedGarbage.Proof.X448.AArch64.Normalize
import VerifiedGarbage.Proof.X448.AArch64.PointwiseFused
import VerifiedGarbage.Proof.X448.AArch64.Row
import VerifiedGarbage.Proof.X448.AArch64.Small
import VerifiedGarbage.Proof.X448.AArch64.Step
import VerifiedGarbage.Proof.X448.AArch64.Weak.BitStep
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.Wide.AccumSquareBody
import VerifiedGarbage.Proof.X448.Wide.AddCoefficient
import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
import VerifiedGarbage.Proof.X448.Wide.Columns
import VerifiedGarbage.Proof.X448.Wide.Fold
import VerifiedGarbage.Proof.X448.Wide.LoadCached
import VerifiedGarbage.Proof.X448.Wide.Mul
import VerifiedGarbage.Proof.X448.Wide.Normalize
import VerifiedGarbage.Proof.X448.Wide.Pack
import VerifiedGarbage.Proof.X448.Wide.Pass
import VerifiedGarbage.Proof.X448.Wide.PassInit
import VerifiedGarbage.Proof.X448.Wide.Reduce
import VerifiedGarbage.Proof.X448.Wide.SymmetricColumn
import VerifiedGarbage.Proof.X448.Wide.TailMul
import VerifiedGarbage.Proof.X448.Wide.TailSquare
import VerifiedGarbage.Proof.X448.Wide.TailStep
import VerifiedGarbage.Proof.X448.Wide.Term
import VerifiedGarbage.Proof.X448.Wide.UnpackRegs
meta import VerifiedGarbage.Proof.Curve448.AArch64.AccumSquareBody
meta import VerifiedGarbage.Proof.Curve448.AArch64.AddEval
meta import VerifiedGarbage.Proof.Curve448.AArch64.Bounds
meta import VerifiedGarbage.Proof.Curve448.AArch64.Collect
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Butterfly
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.ColEnd
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Sqr
meta import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Arith
meta import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
meta import VerifiedGarbage.Proof.Curve448.AArch64.Product
meta import VerifiedGarbage.Proof.Curve448.AArch64.Stage
meta import VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumn
meta import VerifiedGarbage.Proof.Ed448.Scalar
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Pratt
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.AArch64.AddSub
meta import VerifiedGarbage.Proof.X448.AArch64.BitStep
meta import VerifiedGarbage.Proof.X448.AArch64.BitWrite
meta import VerifiedGarbage.Proof.X448.AArch64.Bits
meta import VerifiedGarbage.Proof.X448.AArch64.Carry
meta import VerifiedGarbage.Proof.X448.AArch64.Columns
meta import VerifiedGarbage.Proof.X448.AArch64.Copy
meta import VerifiedGarbage.Proof.X448.AArch64.Decode
meta import VerifiedGarbage.Proof.X448.AArch64.DecodeAll
meta import VerifiedGarbage.Proof.X448.AArch64.DecodeStore
meta import VerifiedGarbage.Proof.X448.AArch64.Finish
meta import VerifiedGarbage.Proof.X448.AArch64.Init
meta import VerifiedGarbage.Proof.X448.AArch64.Initial
meta import VerifiedGarbage.Proof.X448.AArch64.Inv
meta import VerifiedGarbage.Proof.X448.AArch64.Normalize
meta import VerifiedGarbage.Proof.X448.AArch64.PointwiseFused
meta import VerifiedGarbage.Proof.X448.AArch64.Row
meta import VerifiedGarbage.Proof.X448.AArch64.Small
meta import VerifiedGarbage.Proof.X448.AArch64.Step
meta import VerifiedGarbage.Proof.X448.AArch64.Weak.BitStep
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.Wide.AccumSquareBody
meta import VerifiedGarbage.Proof.X448.Wide.AddCoefficient
meta import VerifiedGarbage.Proof.X448.Wide.CoefficientIO
meta import VerifiedGarbage.Proof.X448.Wide.Columns
meta import VerifiedGarbage.Proof.X448.Wide.Fold
meta import VerifiedGarbage.Proof.X448.Wide.LoadCached
meta import VerifiedGarbage.Proof.X448.Wide.Mul
meta import VerifiedGarbage.Proof.X448.Wide.Normalize
meta import VerifiedGarbage.Proof.X448.Wide.Pack
meta import VerifiedGarbage.Proof.X448.Wide.Pass
meta import VerifiedGarbage.Proof.X448.Wide.PassInit
meta import VerifiedGarbage.Proof.X448.Wide.Reduce
meta import VerifiedGarbage.Proof.X448.Wide.SymmetricColumn
meta import VerifiedGarbage.Proof.X448.Wide.TailMul
meta import VerifiedGarbage.Proof.X448.Wide.TailSquare
meta import VerifiedGarbage.Proof.X448.Wide.TailStep
meta import VerifiedGarbage.Proof.X448.Wide.Term
meta import VerifiedGarbage.Proof.X448.Wide.UnpackRegs

/-!
# X448 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant or a counter), satisfiability, and the shared
contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Proof.X448.AArch64 (Pre)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448AArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Fast.x448 s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448AArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448AArch64.pre Proof.X448.x448AArch64.pub
    Impl.X448.AArch64.Fast.x448 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x448_verified :
    Verified AArch64.target Impl.X448.AArch64.Fast.x448 (Spec.X448.x448Contract AArch64.abi) :=
  Verified.of_correct x448_ok x448_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, AArch64.abi, AArch64.argRegs,
      Proof.X448.x448AArch64] [satState] using satState)

end VG.Proof.X448.AArch64.Fast
