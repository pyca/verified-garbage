module

import VerifiedGarbage.Proof.Ed448.AArch64.Base.Main
meta import VerifiedGarbage.Proof.Ed448.AArch64.Base.Main
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
public import VerifiedGarbage.Proof.Ed448.AArch64.CombSum
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
meta import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
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
import VerifiedGarbage.Proof.Ed448.AArch64.Base.Encode
import VerifiedGarbage.Proof.Ed448.AArch64.CombBase
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.Ed448.Scalar
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
import VerifiedGarbage.Proof.X448.AArch64.Initial
import VerifiedGarbage.Proof.X448.AArch64.Inv
import VerifiedGarbage.Proof.X448.AArch64.Normalize
import VerifiedGarbage.Proof.X448.AArch64.PointwiseFused
import VerifiedGarbage.Proof.X448.AArch64.Row
import VerifiedGarbage.Proof.X448.AArch64.Small
import VerifiedGarbage.Proof.X448.AArch64.Step
import VerifiedGarbage.Proof.X448.AArch64.Weak.BitStep
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
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
meta import VerifiedGarbage.Proof.Ed448.AArch64.Base.Encode
meta import VerifiedGarbage.Proof.Ed448.AArch64.CombBase
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
meta import VerifiedGarbage.Proof.Ed448.Formulas
meta import VerifiedGarbage.Proof.Ed448.Scalar
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
meta import VerifiedGarbage.Proof.X448.AArch64.Initial
meta import VerifiedGarbage.Proof.X448.AArch64.Inv
meta import VerifiedGarbage.Proof.X448.AArch64.Normalize
meta import VerifiedGarbage.Proof.X448.AArch64.PointwiseFused
meta import VerifiedGarbage.Proof.X448.AArch64.Row
meta import VerifiedGarbage.Proof.X448.AArch64.Small
meta import VerifiedGarbage.Proof.X448.AArch64.Step
meta import VerifiedGarbage.Proof.X448.AArch64.Weak.BitStep
meta import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
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
# Ed448 base-point multiplication on AArch64: `Verified`

Correctness including the ABI; constant time (by taint tracking: the only
branches are on the counters, every address is an argument or the static's
address plus a constant or a counter, and the digits' masks only select); and
a concrete state satisfying the signature's contract, under the calling
convention with the comb's tables (`Abi.withConsts combConsts`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)
open VG.Proof.X448.AArch64.Base (CombHeld combWords_length combConsts_eq satMem satMem_held)

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

/-- The analysis, of the code without what it does not read, its comb's field operations analysed
once each (`Proof/X448/AArch64/Base/Erase.lean`). -/
theorem scalarBase_check :
    ∃ h, ((taintS [combSym]).check (Taint.ofRegs [.x0, .x1, .x2]) scalarBase h).isSome = true := by
  apply exists_isSome_of_eraseT
  refine Split.exists_isSome (c' := ?c') ?s ?g
  case s =>
    simp only [scalarBase, encode, Code.eraseT, Impl.X448.AArch64.Fast.invert, ops_eraseT, sqn_eraseT]
    exact .refl _
  case g => taint_decide_sum [VG.Proof.Ed448.AArch64.CombBase.combSum, VG.Proof.Ed448.AArch64.addSum, VG.Proof.Ed448.AArch64.powSum]

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase :=
  let ⟨_, hc⟩ := scalarBase_check
  VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h0, h1, h2]⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) hc

theorem scalarBase_baseOk : BaseOk := ⟨scalarBase_ok, scalarBase_ct⟩

/-- The shared contract's precondition, from its facts. -/
theorem scalarBase_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x1, 57⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 57⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 57 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩]) :
    (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

def scalarBaseSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

theorem scalarBase_sat :
    (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)).pre scalarBaseSat := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, scalarBaseSat.mem.readW (scalarBaseSat.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine scalarBase_spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem scalarBase_implies : scalarBaseLocal.Implies
    (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, -, h2, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h2, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨scalarBaseSat, scalarBase_sat⟩

theorem scalarBase_verified :
    Verified AArch64.target scalarBase (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct scalarBase_ok scalarBase_ct scalarBase_implies

end VG.Proof.Ed448.AArch64
