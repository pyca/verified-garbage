module

public import VerifiedGarbage.Proof.X448.AArch64.Base.Main
meta import VerifiedGarbage.Proof.X448.AArch64.Base.Main
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
meta import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
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
import VerifiedGarbage.Proof.X448.AArch64.Iter
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
meta import VerifiedGarbage.Proof.X448.AArch64.Iter
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
# X448 of the base point on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the counters, every address is an argument
or the static's address plus a constant or a counter, and the digits' masks
only select), and the shared contract of `Spec/`, under the calling convention
with the comb's tables (`Abi.withConsts combConsts`).
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64.Base

/-- The analysis, of the code without what it does not read, its comb's field operations analysed
once each (`Base/Erase.lean`). -/
theorem x448Base_check :
    ∃ h, ((taintS [combSym]).check (Taint.ofRegs [.x0, .x1, .x2]) Impl.X448.AArch64.Base.x448Base h).isSome =
      true := by
  apply exists_isSome_of_eraseT
  refine Split.exists_isSome (c' := ?c') ?s ?g
  case s =>
    simp only [x448Base, finish, Code.eraseT, Impl.X448.AArch64.Fast.invert, ops_eraseT, sqn_eraseT]
    exact .refl _
  case g => taint_decide_sum [VG.Proof.Ed448.AArch64.CombBase.combSum, VG.Proof.Ed448.AArch64.addSum, VG.Proof.Ed448.AArch64.powSum]

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseAArch64.pre Proof.X448.x448BaseAArch64.pub
    Impl.X448.AArch64.Base.x448Base :=
  let ⟨_, hc⟩ := x448Base_check
  VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) hc

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x2000, 56⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 56⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x1, 56⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 56⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 56 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 56 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩]) :
    (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

theorem sat_spec : (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)).pre satState := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, satState.mem.readW (satState.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : Proof.X448.x448BaseAArch64.Implies
    (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, -, h2, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h2, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨h0, h1, h2, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

theorem x448Base_ok (s : State) (hs : Proof.X448.x448BaseAArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Base.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448Base_verified :
    Verified AArch64.target Impl.X448.AArch64.Base.x448Base
      (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct x448Base_ok x448Base_ct implies

end VG.Proof.X448.AArch64.Base
