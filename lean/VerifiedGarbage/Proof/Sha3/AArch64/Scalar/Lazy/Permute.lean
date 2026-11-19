module

public import VerifiedGarbage.Proof.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Bitslice.Anf
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
import Mathlib.Tactic.ToExpr
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import Mathlib.Tactic.ToExpr
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Sha3.AArch64.Permute
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics
meta import VerifiedGarbage.Proof.Sha3.AArch64.Permute
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics

/-! ### `Sha3.AArch64.Scalar.Unrolled`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Scalar.Wrap`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Scalar.Restore`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure RestoreInv (orig start : State) (k : Nat) (s : State) : Prop where
  keep : Keep start s
  mem : s.mem = start.mem
  vec : s.v = start.v
  vals : ∀ i < k, s.gpr (savedReg i) = orig.gpr (savedReg i)

theorem restore_ok (orig start : State) (hsave : SavedVector orig start) :
    WP isa (.block restore) start fun s => Keep start s ∧ s.mem = start.mem ∧ s.v = start.v ∧
      ∀ r ∈ preserved, s.gpr r = orig.gpr r := by
  unfold restore
  rw [show (List.range 11).map (fun i => Instr.umov .x (savedReg i) (savedVec i) 0) =
    (List.range 11).flatMap (fun i => [Instr.umov .x (savedReg i) (savedVec i) 0]) by rfl]
  refine (wp_range_flatMap (M := isa) (RestoreInv orig start) (fun i s hi hs => ?_)
    11 (Nat.le_refl _) start ⟨Keep.refl _,rfl,rfl,fun _ h => by omega⟩).mono
    fun s hs => ⟨hs.keep,hs.mem,hs.vec,fun r hr => ?_⟩
  · refine WP.cons (exec_umov_low s (savedReg i) (savedVec i)) (wp_nil ?_)
    refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.mem,hs.vec,fun j hj => ?_⟩
    simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,savedReg_inj j (by omega_using [hi, hj]) i hi]
    split
    · rename_i h; subst j
      rw [hs.vec]
      exact hsave i hi
    · exact hs.vals j (by omega_arith)
  · have hall : ∀ r ∈ preserved, ∃ i : Fin 11, r = savedReg i.val := by decide
    obtain ⟨i,rfl⟩ := hall r hr
    exact hs.vals i.val i.isLt
end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

end

/-! ### `Sha3.AArch64.Scalar.Store`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure StoreInv (s₀ : VG.AArch64.State) (p : Addr) (A : Spec.Sha3.State)
    (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  gpr : s.gpr = s₀.gpr
  vec : s.v = s₀.v
  frame : Frame [⟨p,200⟩] s₀.mem s.mem
  vals : ∀ i (_hi : i < k) (h25 : i < 25), s.mem.readW (p + BitVec.ofNat 64 (8*i)) 64 = A[i]

theorem store_words_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State)
    (hA : Lanes s₀ A)
    (hin : ∀ i < 25, InRegions s₀.wr (s₀.gpr .x30 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block ((List.range 25).map fun i => .str .x (laneReg i) .x30 (8*i)))
      s₀ (StoreInv s₀ (s₀.gpr .x30) A 25) := by
  rw [show (List.range 25).map (fun i => Instr.str .x (laneReg i) .x30 (8*i)) =
    (List.range 25).flatMap (fun i => [Instr.str .x (laneReg i) .x30 (8*i)]) by rfl]
  refine wp_range_flatMap (M := isa) (StoreInv s₀ (s₀.gpr .x30) A) (fun i s hi hs => ?_)
    25 (Nat.le_refl _) s₀ ⟨Keep.refl _,rfl,rfl,Frame.refl _ _,fun _ h => absurd h (by omega_using [])⟩
  refine WP.cons (exec_str_x ⟨by omega_using [],by omega_using [hi]⟩ ?_) (wp_nil ?_)
  · rw [hs.keep.wr,hs.gpr]
    exact hin i hi
  · refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.vec,?_,fun j hj h25 => ?_⟩
    · change Frame _ _ (s.mem.writeW _ _)
      rw [hs.gpr]
      exact hs.frame.writeW (r := ⟨s₀.gpr .x30,200⟩) (by simp) _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
    · change (s.mem.writeW _ _).readW _ 64 = _
      rw [hs.gpr]
      by_cases he : j = i
      · subst j
        rw [Mem.readW_writeW_self64]
        exact hA i hi
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [he]) (by omega_using [h25]) (by omega_using [hi])) (by decide)]
        exact hs.vals j (by omega_using [hj, he]) h25

theorem store_ok (s₀ : VG.AArch64.State) (p : Addr) (A : Spec.Sha3.State)
    (hA : Lanes s₀ A) (hptr : vdword (s₀.v .v30) 0 = p)
    (hin : ∀ i < 25, InRegions s₀.wr (p + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block store) s₀ fun s' => Keep s₀ s' ∧ s'.v = s₀.v ∧
      Frame [⟨p,200⟩] s₀.mem s'.mem ∧ Spec.Sha3.stateAt s'.mem p = A := by
  change (s₀.v .v30).extractLsb' (64*0) 64 = p at hptr
  unfold store
  refine WP.cons rfl ?_
  refine (store_words_ok _ A ?_ ?_).mono fun s hs => ?_
  · intro i hi
    simpa only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,laneReg_ne_x30 i hi,ite_false]
      using hA i hi
  · intro i hi
    simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,RegUpd.wr_write,hptr] using hin i hi
  · have hb : (s₀.write .x .x30 ((s₀.v .v30).extractLsb' (64*0) 64)).gpr .x30 = p := by
      simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,vdword] using hptr
    refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.vec,?_,?_⟩
    · simpa only [hb,RegUpd.mem_write] using hs.frame
    · apply Vector.ext
      intro i hi
      simpa only [Spec.Sha3.stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr,hb]
        using hs.vals i hi hi

end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

end

/-! ### `Sha3.AArch64.Scalar.Load`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure LoadInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  mem : s.mem = s₀.mem
  vec : s.v = s₀.v
  base : s.gpr .x30 = s₀.gpr .x0
  lanes : ∀ j < k, s.gpr (laneReg j) =
    s₀.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 (8*j)) 64

theorem load_ok (s₀ : VG.AArch64.State)
    (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block load) s₀ fun s' => Keep s₀ s' ∧ s'.mem = s₀.mem ∧ s'.v = s₀.v ∧
      Lanes s' (Spec.Sha3.stateAt s₀.mem (s₀.gpr .x0)) := by
  have hrun : ∀ s, LoadInv s₀ 0 s →
      WP isa (.block ((List.range 25).map fun i => .ldr .x (laneReg i) .x30 (8*i)))
        s (LoadInv s₀ 25) := by
    intro s hs
    rw [show (List.range 25).map (fun i => Instr.ldr .x (laneReg i) .x30 (8*i)) =
      (List.range 25).flatMap (fun i => [Instr.ldr .x (laneReg i) .x30 (8*i)]) by rfl]
    refine wp_range_flatMap (M := isa) (LoadInv s₀) (fun i s hi hs => ?_)
      25 (Nat.le_refl _) s hs
    refine WP.cons (exec_ldr_x ⟨by omega_using [],by omega_using [hi]⟩ ?_) (wp_nil ?_)
    · rw [hs.keep.rd,hs.keep.wr,hs.base]
      exact hin i hi
    · refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.mem,hs.vec,?_,fun j hj => ?_⟩
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          Ne.symm (laneReg_ne_x30 i hi),ite_false,hs.base]
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          laneReg_inj j (by omega_using [hi, hj]) i hi]
        split
        · rename_i he; subst j
          rw [hs.mem,hs.base]
        · exact hs.lanes j (by omega_arith)
  unfold load
  refine WP.cons (exec_addImm_x (by decide)) ?_
  refine (hrun _ ?_).mono fun s hs => ⟨hs.keep,hs.mem,hs.vec,?_⟩
  · refine ⟨⟨rfl,rfl,rfl⟩,rfl,rfl,?_,fun _ h => absurd h (by omega_using [])⟩
    simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
      show BitVec.ofNat 64 0 = 0 by rfl]
    exact BitVec.add_zero _
  · intro i hi
    simpa only [Spec.Sha3.stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr] using hs.lanes i hi

end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

end

/-! ### `Sha3.AArch64.Scalar.Save`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure SaveInv (orig : State) (k : Nat) (s : State) : Prop where
  keep : Keep orig s
  gpr : s.gpr = orig.gpr
  mem : s.mem = orig.mem
  vals : ∀ i < k, vdword (s.v (savedVec i)) 0 = orig.gpr (savedReg i)
  vec : ∀ r ∈ preservedV, s.v r = orig.v r

theorem save_vectors_ok (orig : State) :
    WP isa (.block ((List.range 11).map fun i => .vop (.dup .d2 (savedVec i) (savedReg i))))
      orig (SaveInv orig 11) := by
  rw [show (List.range 11).map (fun i => Instr.vop (.dup .d2 (savedVec i) (savedReg i))) =
    (List.range 11).flatMap (fun i => [Instr.vop (.dup .d2 (savedVec i) (savedReg i))]) by rfl]
  refine wp_range_flatMap (M := isa) (SaveInv orig) (fun i s hi hs => ?_)
    11 (Nat.le_refl _) orig ⟨Keep.refl _,rfl,rfl,fun _ h => by omega,fun _ _ => rfl⟩
  refine WP.cons rfl (wp_nil ?_)
  refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.mem,fun j hj => ?_,fun r hr => ?_⟩
  · simp only [RegUpd.v_setV,savedVec_inj j (by omega_using [hi, hj]) i hi]
    split
    · rename_i h; subst j
      simp only [vdword_ofVDwords_0,hs.gpr]
    · exact hs.vals j (by omega_arith)
  · simp only [RegUpd.v_setV,savedVec_not_preserved i hi r hr,ite_false]
    exact hs.vec r hr

theorem save_ok (orig : State) :
    WP isa (.block save) orig fun s => Keep orig s ∧ s.gpr = orig.gpr ∧
      s.mem = orig.mem ∧ SavedVector orig s ∧ Ptrs orig s ∧
      (∀ r ∈ preservedV, s.v r = orig.v r) := by
  unfold save
  rw [WP.block_append_iff]
  refine (save_vectors_ok orig).mono fun s hs => ?_
  refine WP.cons rfl (WP.cons rfl (wp_nil ?_))
  refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.mem,?_,?_,?_⟩
  · intro i hi
    have hn := savedVec_ne_ptrs i hi
    simp only [RegUpd.v_setV,hn.1,hn.2,ite_false]
    exact hs.vals i hi
  · simp only [Ptrs,RegUpd.v_setV,reduceCtorEq,ite_false,ite_true,
      vdword_ofVDwords_0,RegUpd.gpr_setV,hs.gpr]
    exact ⟨True.intro,True.intro⟩
  · intro r hr
    have hn : ∀ r ∈ preservedV, r ≠ .v30 ∧ r ≠ .v31 := by decide
    simp only [RegUpd.v_setV,(hn r hr).1,(hn r hr).2,ite_false]
    exact hs.vec r hr
end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

end

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

/-- The middle may use every GPR but must retain public pointers, saved GPRs,
and the ABI-protected vector registers. -/
structure CoreState (orig : VG.AArch64.State) (A : Spec.Sha3.State) (s : VG.AArch64.State) : Prop where
  keep : Keep orig s
  ptrs : Ptrs orig s
  saved : SavedVector orig s
  vec : ∀ r ∈ preservedV, s.v r = orig.v r
  lanes : Lanes s A

theorem wrap_correct (middle : Prog isa)
    (hmid : ∀ orig A s, VG.Proof.Sha3.AArch64.Pre orig → CoreState orig A s →
      WP isa middle s (CoreState orig (Spec.Sha3.keccakF A)))
    (orig : VG.AArch64.State) (hp : VG.Proof.Sha3.AArch64.Pre orig) :
    WP isa (wrap middle) orig fun s' => abiPreserved orig s' ∧
      VG.Proof.Sha3.permuteAArch64.post orig s' := by
  unfold wrap
  rw [WP.seq_iff]
  refine (save_ok orig).mono fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  refine (load_ok s₁ (fun i hi => ?_)).mono fun s₂ h₂ => ?_
  · rw [h₁.1.rd,h₁.1.wr,h₁.2.1]
    exact hp.in_all (hp.lane_in (.inl rfl) hi)
  · have ha : Lanes s₂ (Spec.Sha3.stateAt orig.mem (orig.gpr .x0)) := by
      have hst : Spec.Sha3.stateAt s₁.mem (s₁.gpr .x0) =
          Spec.Sha3.stateAt orig.mem (orig.gpr .x0) := by rw [h₁.2.1, h₁.2.2.1]
      rw [hst] at h₂
      exact h₂.2.2.2
    have hs₂ : CoreState orig (Spec.Sha3.stateAt orig.mem (orig.gpr .x0)) s₂ := by
      refine ⟨h₁.1.trans h₂.1,?_,?_,?_,ha⟩
      · simpa only [Ptrs,h₂.2.2.1] using h₁.2.2.2.2.1
      · simpa only [SavedVector,h₂.2.2.1] using h₁.2.2.2.1
      · intro r hr
        rw [h₂.2.2.1]
        exact h₁.2.2.2.2.2 r hr
    rw [WP.seq_iff]
    refine (hmid orig _ s₂ hp hs₂).mono fun s₃ h₃ => ?_
    rw [WP.seq_iff]
    refine (store_ok s₃ (orig.gpr .x0) _ h₃.lanes h₃.ptrs.1 (fun i hi => ?_)).mono
      fun s₄ h₄ => ?_
    · rw [h₃.keep.wr]
      exact hp.lane_in (.inl rfl) hi
    · have hs₄ : SavedVector orig s₄ := by
        simpa only [SavedVector,h₄.2.1] using h₃.saved
      refine (restore_ok orig s₄ hs₄).mono fun s' h₅ => ?_
      refine ⟨⟨h₅.2.2.2,h₅.1.sp.trans (h₄.1.sp.trans h₃.keep.sp),?_⟩,?_⟩
      · intro r hr
        rw [h₅.2.2.1,h₄.2.1,h₃.vec r hr]
      · change Spec.Sha3.stateAt s'.mem (orig.gpr .x0) = _
        rw [h₅.2.1]
        exact h₄.2.2.2

end VG.Proof.Sha3.AArch64.Scalar.Boundary

end

end

/-!
# The scalar rounds: what they keep

What the scalar rounds keep besides `Boundary.CoreState`, the middle's
contract in `wrap_correct`: memory, and the AdvSIMD registers other than
the core's temporaries (`RoundKeep`), which the registers the boundary
saves and the callee-saved ones are not among (`savedVec_not_temps`,
`preservedV_not_temps`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar.Boundary

theorem savedVec_not_temps : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v24 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v25 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v28 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v29 := by decide

theorem preservedV_not_temps : ∀ r ∈ preservedV, r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v28 ∧ r ≠ .v29 := by
  decide

/-- What the rounds keep besides the boundary's invariant: memory, and the
AdvSIMD registers other than the core's temporaries. -/
structure RoundKeep (s t : State) : Prop where
  mem : t.mem = s.mem
  v : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → t.v v = s.v v

end VG.Proof.Sha3.AArch64.Scalar

end

end

/-! ### `Sha3.AArch64.Scalar.Lazy.Round`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Scalar.Lazy`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Scalar.RotateExpr`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

/-- Push rotations to leaves. Deferred rotations can then be checked without
expanding an entire 24-round permutation into one expression tree. -/
def Expr.rotateNormal : Expr → Nat → Expr
  | .reg r, n => .ror (.reg r) (n % 64)
  | .slot k, n => .ror (.slot k) (n % 64)
  | .xor a b, n => .xor (a.rotateNormal n) (b.rotateNormal n)
  | .bic a b, n => .bic (a.rotateNormal n) (b.rotateNormal n)
  | .ror a k, n => a.rotateNormal ((k + n) % 64)

theorem rotateRight_not (x : Lane) (n : Nat) :
    (~~~x).rotateRight n = ~~~(x.rotateRight n) := by
  ext i hi
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_not]
  split <;> rfl

theorem Expr.rotateNormal_eval (e : Expr) (f : File) (n : Nat) :
    (e.rotateNormal n).eval f = (e.eval f).rotateRight n := by
  induction e generalizing n with
  | reg r => exact BitVec.rotateRight_mod_eq_rotateRight
  | slot k => exact BitVec.rotateRight_mod_eq_rotateRight
  | xor a b ha hb =>
    simp only [rotateNormal, Expr.eval, ha, hb, VG.Bitslice.Anf.rotateRight_xor]
  | bic a b ha hb =>
    simp only [rotateNormal, Expr.eval, ha, hb, VG.Bitslice.Anf.rotateRight_and,
      rotateRight_not]
  | ror a k ha =>
    simp only [rotateNormal, Expr.eval, ha, VG.Bitslice.Anf.rotateRight_rotateRight]

end VG.Proof.Sha3.AArch64.Scalar

end

end


@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

deriving instance DecidableEq for ScalarOp

def registers : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30]
def regIndex (r : Reg) : Nat := registers.idxOf r

def environment (logical physical : File) : File :=
  ⟨logical.regs, fun k => if k % 2 = 0 then physical.slots (k / 2)
    else physical.regs (registers.getD (k / 2) .x0)⟩

/-- Unassigned registers and preexisting slots are distinct symbolic inputs. -/
def physicalInitial : SymFile :=
  ⟨fun r => .slot (2 * regIndex r + 1), fun k => .slot (2 * k)⟩

/-- Model the physical input lanes by expressions in canonical logical lanes. -/
def symbolicLayout (layout : Layout) : SymFile :=
  layout.zipIdx.foldl (fun sf (entry, i) =>
    sf.write entry.1 (.ror (.reg (laneReg i)) entry.2)) physicalInitial

theorem environment_reg (logical physical : File) (r : Reg) :
    (Expr.slot (2 * regIndex r + 1)).eval (environment logical physical) = physical.regs r := by
  cases r <;> rfl

theorem physicalInitial_compatible (logical physical : File) :
    Compatible (environment logical physical) physicalInitial physical := by
  constructor
  · intro r; exact (environment_reg logical physical r).symm
  · intro k
    simp only [physicalInitial, Expr.eval, environment]
    rw [show 2 * k % 2 = 0 by omega_using [], ite_eq_left rfl,
      show 2 * k / 2 = k by omega_using []]

/-- Every listed lane has its declared physical orientation. -/
def LayoutHolds (layout : Layout) (logical physical : File) : Prop :=
  ∀ entry i, (entry, i) ∈ layout.zipIdx →
    physical.regs entry.1 = (logical.regs (laneReg i)).rotateRight entry.2

theorem symbolicLayout_compatible (layout : Layout) (logical physical : File)
    (h : LayoutHolds layout logical physical) :
    Compatible (environment logical physical) (symbolicLayout layout) physical := by
  apply List.foldlRecOn (motive := fun sf =>
    Compatible (environment logical physical) sf physical)
  · exact physicalInitial_compatible logical physical
  · intro sf hs entry he
    obtain ⟨⟨reg, offset⟩, i⟩ := entry
    constructor
    · intro q
      simp only [SymFile.write]
      split
      · rename_i hq; subst q
        exact h (reg, offset) i he
      · exact hs.1 q
    · exact hs.2

def outputExpr (p : Plan) (i : Nat) : Expr :=
  let (reg, offset) := p.output.getD i (.x0, 0)
  ((symRun p.core (symbolicLayout p.input)).regs reg).rotateNormal ((64-offset)%64)

def referenceExpr (i : Nat) : Expr :=
  ((symRun coreOps symInitial).regs (laneReg i)).rotateNormal 0

theorem plan_math (p : Plan)
    (cert : ∀ i < 25, outputExpr p i = referenceExpr i)
    (logical physical : File) (h : LayoutHolds p.input logical physical)
    (i : Nat) (hi : i < 25) :
    let (reg, offset) := p.output.getD i (.x0, 0)
    ((run p.core physical).regs reg).rotateRight ((64-offset)%64) =
      (run coreOps (environment logical physical)).regs (laneReg i) := by
  have hc := symRun_correct (environment logical physical) physical
    (symbolicLayout p.input) p.core (symbolicLayout_compatible p.input logical physical h)
  have he := congrArg (Expr.eval (environment logical physical)) (cert i hi)
  dsimp only [outputExpr, referenceExpr] at he
  rw [Expr.rotateNormal_eval, Expr.rotateNormal_eval,
    VG.Bitslice.Anf.rotateRight_zero, ← run_regs] at he
  rw [← hc.1] at he
  rcases hp : p.output.getD i (.x0, 0) with ⟨reg, offset⟩
  simpa only [hp] using he

theorem rotateRight_undo (x : Lane) (offset : Nat) (ho : offset < 64) :
    (x.rotateRight ((64-offset)%64)).rotateRight offset = x := by
  rw [VG.Bitslice.Anf.rotateRight_rotateRight]
  have hm : (((64-offset)%64)+offset)%64 = 0 := by omega_using [ho]
  rw [hm, VG.Bitslice.Anf.rotateRight_zero]

theorem plan_layout (p : Plan)
    (cert : ∀ i < 25, outputExpr p i = referenceExpr i)
    (hlen : p.output.length = 25)
    (bounds : ∀ entry ∈ p.output, entry.2 < 64)
    (logical physical : File) (h : LayoutHolds p.input logical physical) :
    LayoutHolds p.output (run coreOps (environment logical physical)) (run p.core physical) := by
  intro entry i he
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp he
  have hi : i < 25 := by
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    omega_using [hlen, hlt]
  have hd : p.output.getD i (.x0, 0) = entry := by
    simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  have hm := plan_math p cert logical physical h i hi
  simp only [hd] at hm
  have hb : entry.2 < 64 := bounds entry (List.mem_of_getElem? hget)
  have ht := congrArg (fun x : Lane => x.rotateRight entry.2) hm
  rw [rotateRight_undo _ _ hb] at ht
  exact ht

/-! ## The certificate, for the kernel

`outputExpr` reads a `SymFile`, a chain of functions that the kernel follows again for every
read, and compares two trees of a hundred nodes for every lane of every round. The kernel checks
the same run with

* the registers in a structure (`KF`), read by a projection and written by rebuilding it;
* expressions read from a register evaluated before they are used (`force`), and rotations
  evaluated before they are passed down (`forceNat`), so that a subexpression several lanes
  share is the same term in each, and the kernel finds again what it did with it;
* the comparison in `Bool` (`same`): `DecidableEq`'s answer for two applications carries a
  cast along the equation of their arguments, which the kernel reduces by comparing them as the
  terms they are. -/

/-- `k e`, with `e` evaluated to its constructor. -/
private def force {α : Type} (e : Expr) (k : Expr → α) : α :=
  Expr.casesOn (motive := fun _ => α) e (fun r => k (.reg r)) (fun s => k (.slot s))
    (fun a b => k (.xor a b)) (fun a b => k (.bic a b)) (fun a n => k (.ror a n))

private theorem force_eq {α : Type} (e : Expr) (k : Expr → α) : force e k = k e := by cases e <;> rfl

/-- `k n`, with `n` evaluated to a numeral. -/
private def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (motive := fun _ => α) (Nat.succ n) (k n) (fun m => k m)

private theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := rfl

/-- The registers' expressions, a field each. -/
private structure KF where
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x30 : Expr)
  slots : Nat → Expr

private def KF.get (f : KF) (r : Reg) : Expr :=
  (match r with
    | .x0 => KF.x0 | .x1 => KF.x1 | .x2 => KF.x2 | .x3 => KF.x3 | .x4 => KF.x4 | .x5 => KF.x5
    | .x6 => KF.x6 | .x7 => KF.x7 | .x8 => KF.x8 | .x9 => KF.x9 | .x10 => KF.x10 | .x11 => KF.x11
    | .x12 => KF.x12 | .x13 => KF.x13 | .x14 => KF.x14 | .x15 => KF.x15 | .x16 => KF.x16
    | .x17 => KF.x17 | .x19 => KF.x19 | .x20 => KF.x20 | .x21 => KF.x21 | .x22 => KF.x22
    | .x23 => KF.x23 | .x24 => KF.x24 | .x25 => KF.x25 | .x26 => KF.x26 | .x27 => KF.x27
    | .x28 => KF.x28 | .x30 => KF.x30) f

private def KF.write (f : KF) (d : Reg) (v : Expr) : KF :=
  (match d with
    | .x0 => fun f v => { f with x0 := v } | .x1 => fun f v => { f with x1 := v }
    | .x2 => fun f v => { f with x2 := v } | .x3 => fun f v => { f with x3 := v }
    | .x4 => fun f v => { f with x4 := v } | .x5 => fun f v => { f with x5 := v }
    | .x6 => fun f v => { f with x6 := v } | .x7 => fun f v => { f with x7 := v }
    | .x8 => fun f v => { f with x8 := v } | .x9 => fun f v => { f with x9 := v }
    | .x10 => fun f v => { f with x10 := v } | .x11 => fun f v => { f with x11 := v }
    | .x12 => fun f v => { f with x12 := v } | .x13 => fun f v => { f with x13 := v }
    | .x14 => fun f v => { f with x14 := v } | .x15 => fun f v => { f with x15 := v }
    | .x16 => fun f v => { f with x16 := v } | .x17 => fun f v => { f with x17 := v }
    | .x19 => fun f v => { f with x19 := v } | .x20 => fun f v => { f with x20 := v }
    | .x21 => fun f v => { f with x21 := v } | .x22 => fun f v => { f with x22 := v }
    | .x23 => fun f v => { f with x23 := v } | .x24 => fun f v => { f with x24 := v }
    | .x25 => fun f v => { f with x25 := v } | .x26 => fun f v => { f with x26 := v }
    | .x27 => fun f v => { f with x27 := v } | .x28 => fun f v => { f with x28 := v }
    | .x30 => fun f v => { f with x30 := v } : KF → Expr → KF) f v

/-- The registers' expressions, in the order of `registers`. -/
private def KF.toList (f : KF) : List Expr :=
  [f.x0, f.x1, f.x2, f.x3, f.x4, f.x5, f.x6, f.x7, f.x8, f.x9, f.x10, f.x11, f.x12, f.x13,
    f.x14, f.x15, f.x16, f.x17, f.x19, f.x20, f.x21, f.x22, f.x23, f.x24, f.x25, f.x26, f.x27,
    f.x28, f.x30]

private theorem KF.get_toList (f : KF) (r : Reg) : f.get r = f.toList.getD r.ctorIdx (.slot 0) := by
  cases r <;> rfl

private theorem KF.toList_write (f : KF) (d : Reg) (v : Expr) :
    (f.write d v).toList = f.toList.set d.ctorIdx v := by
  cases d <;> rfl

private theorem ctorIdx_inj {q d : Reg} (h : q.ctorIdx = d.ctorIdx) : q = d := by
  have e : ∀ r : Reg, registers.getD r.ctorIdx .x0 = r := fun r => by cases r <;> rfl
  rw [← e q, ← e d, h]

/-- By the list of the fields: a case for each register, not for each pair. -/
private theorem KF.get_write (f : KF) (d q : Reg) (v : Expr) :
    (f.write d v).get q = if q = d then v else f.get q := by
  by_cases h : q = d
  · subst h; rw [ite_eq_left rfl]; cases q <;> rfl
  · rw [ite_eq_right h, KF.get_toList, KF.toList_write, KF.get_toList, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_set_ne fun e => h (ctorIdx_inj e.symm)]

private theorem KF.slots_write (f : KF) (d : Reg) (v : Expr) : (f.write d v).slots = f.slots := by
  cases d <;> rfl

private def KF.ofFn (g : Reg → Expr) (sl : Nat → Expr) : KF :=
  ⟨g .x0, g .x1, g .x2, g .x3, g .x4, g .x5, g .x6, g .x7, g .x8, g .x9, g .x10, g .x11, g .x12,
    g .x13, g .x14, g .x15, g .x16, g .x17, g .x19, g .x20, g .x21, g .x22, g .x23, g .x24,
    g .x25, g .x26, g .x27, g .x28, g .x30, sl⟩

/-- A `KF` holds what a `SymFile` does. -/
private def Agree (sf : SymFile) (f : KF) : Prop := (∀ r, sf.regs r = f.get r) ∧ sf.slots = f.slots

private theorem KF.ofFn_agree (g : Reg → Expr) (sl : Nat → Expr) : Agree ⟨g, sl⟩ (KF.ofFn g sl) :=
  ⟨fun r => by cases r <;> rfl, rfl⟩

private theorem Agree.write {sf : SymFile} {f : KF} (h : Agree sf f) (d : Reg) (v : Expr) :
    Agree (sf.write d v) (f.write d v) :=
  ⟨fun q => by rw [KF.get_write, ← h.1 q]; rfl, by rw [KF.slots_write]; exact h.2⟩

/-- `symStep`, on a `KF`, with the operands evaluated. -/
private def kStepF (f : KF) : ScalarOp → KF
  | .xor d a b => force (f.get a) fun x => force (f.get b) fun y => f.write d (.xor x y)
  | .xorRor d a b n => force (f.get a) fun x => force (f.get b) fun y => f.write d (.xor x (.ror y n))
  | .bic d a b => force (f.get a) fun x => force (f.get b) fun y => f.write d (.bic x y)
  | .bicRor d a b n => force (f.get a) fun x => force (f.get b) fun y => f.write d (.bic x (.ror y n))
  | .ror d a n => force (f.get a) fun x => f.write d (.ror x n)
  | .move d a => force (f.get a) fun x => f.write d x
  | .spill k a => force (f.get a) fun x => { f with slots := fun j => if j = k then x else f.slots j }
  | .reload d k => force (f.slots k) fun x => f.write d x

private def kRunF (ops : List ScalarOp) (f : KF) : KF := ops.foldl kStepF f

private theorem kStepF_agree {sf : SymFile} {f : KF} (h : Agree sf f) (op : ScalarOp) :
    Agree (symStep sf op) (kStepF f op) := by
  cases op <;> simp only [kStepF, symStep, force_eq, h.1, h.2]
  case spill k a => exact ⟨fun r => by cases r <;> exact h.1 _, rfl⟩
  all_goals exact h.write _ _

private theorem kRunF_agree {sf : SymFile} {f : KF} (h : Agree sf f) (ops : List ScalarOp) :
    Agree (symRun ops sf) (kRunF ops f) := by
  induction ops generalizing sf f with
  | nil => exact h
  | cons op ops ih => exact ih (kStepF_agree h op)

/-- `symbolicLayout`, as a `KF`. -/
private def kLayoutF (layout : Layout) : KF :=
  layout.zipIdx.foldl (fun kf (entry, i) =>
    kf.write entry.1 (.ror (.reg (laneReg i)) entry.2))
    (KF.ofFn (fun r => .slot (2 * regIndex r + 1)) fun k => .slot (2 * k))

private theorem kLayoutF_agree (layout : Layout) : Agree (symbolicLayout layout) (kLayoutF layout) := by
  unfold symbolicLayout kLayoutF
  have h : Agree physicalInitial
      (KF.ofFn (fun r => .slot (2 * regIndex r + 1)) fun k => .slot (2 * k)) := KF.ofFn_agree _ _
  generalize layout.zipIdx = l
  generalize physicalInitial = sf at h ⊢
  generalize KF.ofFn (fun r => .slot (2 * regIndex r + 1)) (fun k => .slot (2 * k)) = kf at h ⊢
  induction l generalizing sf kf with
  | nil => exact h
  | cons e l ih => exact ih _ _ (h.write e.1.1 _)

/-- `Expr.rotateNormal`, with the rotation it passes down evaluated. By the recursor, whose
cases are closed terms: the kernel instantiates nothing to unfold it. -/
private noncomputable def norm (e : Expr) : Nat → Expr :=
  Expr.rec (motive := fun _ => Nat → Expr)
    (fun r n => .ror (.reg r) (n % 64))
    (fun k n => .ror (.slot k) (n % 64))
    (fun _ _ na nb n => .xor (na n) (nb n))
    (fun _ _ na nb n => .bic (na n) (nb n))
    (fun _ k na n => forceNat ((k + n) % 64) fun m => na m) e

private theorem norm_eq (e : Expr) (n : Nat) : norm e n = e.rotateNormal n := by
  induction e generalizing n with
  | reg r => rfl
  | slot k => rfl
  | xor a b ha hb => rw [Expr.rotateNormal, ← ha, ← hb]; rfl
  | bic a b ha hb => rw [Expr.rotateNormal, ← ha, ← hb]; rfl
  | ror a k ha => exact ha ((k + n) % 64)

/-- Whether two expressions are the same. -/
private noncomputable def same (a : Expr) : Expr → Bool :=
  Expr.rec (motive := fun _ => Expr → Bool)
    (fun r b => match b with | .reg q => decide (r = q) | _ => false)
    (fun k b => match b with | .slot j => decide (k = j) | _ => false)
    (fun _ _ sa sb b => match b with | .xor c d => sa c && sb d | _ => false)
    (fun _ _ sa sb b => match b with | .bic c d => sa c && sb d | _ => false)
    (fun _ n sa b => match b with | .ror c m => decide (n = m) && sa c | _ => false) a

private theorem eq_of_same {a b : Expr} (h : same a b = true) : a = b := by
  induction a generalizing b with
  | reg r => cases b <;> first | exact absurd h Bool.false_ne_true | exact congrArg _ (of_decide_eq_true h)
  | slot k => cases b <;> first | exact absurd h Bool.false_ne_true | exact congrArg _ (of_decide_eq_true h)
  | xor a₁ a₂ h₁ h₂ =>
    cases b with
    | xor c d => have h' := Bool.and_eq_true_iff.mp h; rw [h₁ h'.1, h₂ h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | bic a₁ a₂ h₁ h₂ =>
    cases b with
    | bic c d => have h' := Bool.and_eq_true_iff.mp h; rw [h₁ h'.1, h₂ h'.2]
    | _ => exact absurd h Bool.false_ne_true
  | ror a₁ n h₁ =>
    cases b with
    | ror c m => have h' := Bool.and_eq_true_iff.mp h; rw [h₁ h'.2, of_decide_eq_true h'.1]
    | _ => exact absurd h Bool.false_ne_true

/-- `outputExpr`, as the kernel evaluates it. -/
private noncomputable def outputExprF (p : Plan) (i : Nat) : Expr :=
  forceNat ((64 - (p.output.getD i (.x0, 0)).2) % 64) fun n =>
    norm ((kRunF p.core (kLayoutF p.input)).get (p.output.getD i (.x0, 0)).1) n

/-- `referenceExpr`, as the kernel evaluates it. -/
private noncomputable def referenceExprF (i : Nat) : Expr :=
  norm ((kRunF coreOps (KF.ofFn Expr.reg Expr.slot)).get (laneReg i)) 0

private theorem outputExpr_f (p : Plan) (i : Nat) : outputExpr p i = outputExprF p i := by
  rw [outputExprF, forceNat_eq, norm_eq, ← (kRunF_agree (kLayoutF_agree p.input) p.core).1]
  rfl

private theorem referenceExpr_f (i : Nat) : referenceExpr i = referenceExprF i := by
  have h : Agree symInitial (KF.ofFn Expr.reg Expr.slot) := KF.ofFn_agree _ _
  rw [referenceExpr, referenceExprF, norm_eq, ← (kRunF_agree h coreOps).1]

private theorem plans_symbolic_f : ∀ (r : Fin 24), ∀ i < 25,
    same (outputExprF (plans[r.val]' (by exact r.isLt)) i) (referenceExprF i) = true := by
  decide +kernel

theorem plans_symbolic : ∀ (r : Fin 24), ∀ i < 25, outputExpr (plans[r.val]' (by exact r.isLt)) i = referenceExpr i :=
  fun r i hi => by
    rw [outputExpr_f, referenceExpr_f]; exact eq_of_same (plans_symbolic_f r i hi)

theorem plans_shape : ∀ r : Fin 24,
    (plan r).input.length = 25 ∧ (plan r).output.length = 25 ∧
    (plan r).finish = (plan r).output ∧
    (∀ entry ∈ (plan r).output, entry.2 < 64) ∧
    (∀ op ∈ (plan r).core, Good op) ∧ Good (plan r).iota := by decide +kernel

theorem plans_iota : ∀ r : Fin 24,
    let lane := (plan r).output.getD 0 (.x0, 0)
    (plan r).iota = .xorRor lane.1 lane.1 (plan r).constantReg lane.2 ∧
    (∀ entry ∈ (plan r).output, entry.1 ≠ (plan r).constantReg) := by decide +kernel

theorem plans_lane_zero : ∀ r : Fin 24, ∀ i < 25,
    ((plan r).output.getD i (.x0, 0)).1 =
      ((plan r).output.getD 0 (.x0, 0)).1 ↔ i = 0 := by decide +kernel

theorem normalize_symbolic : ∀ i < 25,
    ((symRun normalize (symbolicLayout (plan ⟨23, by decide⟩).finish)).regs
      (laneReg i)).rotateNormal 0 = (Expr.reg (laneReg i)).rotateNormal 0 := by decide +kernel

def stageLayout (n : Nat) : Layout :=
  if h : n < 24 then (plan ⟨n, h⟩).input else (plan ⟨23, by decide⟩).finish

theorem plans_stage : ∀ r : Fin 24, (plan r).finish = stageLayout (r.val+1) := by
  decide +kernel

theorem normalize_good : ∀ op ∈ normalize, Good op := by decide +kernel

end VG.Proof.Sha3.AArch64.Scalar.Lazy

end

end

/-! ### `Sha3.AArch64.Scalar.Lazy.Math`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

/-- Canonical logical lanes, independent of their current physical allocation. -/
def logicalState (A : Spec.Sha3.State) : File :=
  ⟨(fun r => match r with
    | .x0 => A[0]
    | .x1 => A[1]
    | .x2 => A[2]
    | .x3 => A[3]
    | .x4 => A[4]
    | .x5 => A[5]
    | .x6 => A[6]
    | .x7 => A[7]
    | .x8 => A[8]
    | .x9 => A[9]
    | .x10 => A[10]
    | .x11 => A[11]
    | .x12 => A[12]
    | .x13 => A[13]
    | .x14 => A[14]
    | .x15 => A[15]
    | .x16 => A[16]
    | .x17 => A[17]
    | .x25 => A[18]
    | .x19 => A[19]
    | .x20 => A[20]
    | .x21 => A[21]
    | .x22 => A[22]
    | .x23 => A[23]
    | .x24 => A[24]
    | _ => 0), fun _ => 0⟩

theorem logicalState_lane (A : Spec.Sha3.State) (i : Nat) (hi : i < 25) :
    (logicalState A).regs (laneReg i) = A[i] := by
  iterate 25 (rcases i with _ | i; rfl)
  exact absurd hi (by omega_arith)

/-- A round's scalar operations compute chi/pi/rho/theta in the declared layout. -/
theorem plan_core_state (r : Fin 24) (A : Spec.Sha3.State) (f : File)
    (h : LayoutHolds (plan r).input (logicalState A) f) :
    LayoutHolds (plan r).output
      (logicalState (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A)))))
      (run (plan r).core f) := by
  have hp := plans_shape r
  have hm := plan_layout (plan r) (plans_symbolic r) hp.2.1 hp.2.2.2.1
    (logicalState A) f h
  have hcore := core_math A (environment (logicalState A) f)
    (fun i hi => logicalState_lane A i hi)
  intro entry i he
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp he
  have hi : i < 25 := by
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    omega
  rw [hm entry i he, hcore i hi, logicalState_lane _ i hi]

theorem layout_at (layout : Layout) (logical physical : File)
    (h : LayoutHolds layout logical physical) (i : Nat) (hi : i < layout.length) :
    physical.regs (layout.getD i (.x0, 0)).1 =
      (logical.regs (laneReg i)).rotateRight (layout.getD i (.x0, 0)).2 := by
  apply h _ i
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem layout_of_at (layout : Layout) (logical physical : File)
    (h : ∀ i < layout.length,
      physical.regs (layout.getD i (.x0, 0)).1 =
        (logical.regs (laneReg i)).rotateRight (layout.getD i (.x0, 0)).2) :
    LayoutHolds layout logical physical := by
  intro entry i he
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp he
  have hi := (List.getElem?_eq_some_iff.mp hg).1
  have hd : layout.getD i (.x0, 0) = entry := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  simpa only [hd] using h i hi

theorem plan_iota_state (r : Fin 24) (A : Spec.Sha3.State) (f : File)
    (h : LayoutHolds (plan r).output (logicalState A) f) :
    LayoutHolds (plan r).finish (logicalState (Spec.Sha3.iota A r.val))
      (step (f.write (plan r).constantReg (Spec.Sha3.RC r.val)) (plan r).iota) := by
  have hp := plans_shape r
  rw [hp.2.2.1]
  apply layout_of_at
  intro i hi
  have hi25 : i < 25 := by omega
  have hval := layout_at _ _ _ h i hi
  rw [logicalState_lane A i hi25] at hval
  have hval0 := layout_at _ _ _ h 0 (by omega_using [hi])
  rw [logicalState_lane A 0 (by decide)] at hval0
  have hc := (plans_iota r).2
  have memi : (plan r).output.getD i (.x0, 0) ∈ (plan r).output := by
    apply List.mem_of_getElem? (i := i)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have mem0 : (plan r).output.getD 0 (.x0, 0) ∈ (plan r).output := by
    apply List.mem_of_getElem? (i := 0)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < (plan r).output.length by omega_using [hi]), Option.getD_some]
  rw [(plans_iota r).1]
  simp only [step, File.write, logicalState_lane _ i hi25]
  by_cases hz : i = 0
  · subst i
    simp only [ite_true, ite_eq_right (hc _ mem0), hval0, Spec.Sha3.iota,
      Vector.getElem_set_self, VG.Bitslice.Anf.rotateRight_xor]
  · have hn := (not_congr (plans_lane_zero r i hi25)).mpr hz
    simp only [ite_eq_right hn, ite_eq_right (hc _ memi), hval,
      Spec.Sha3.iota, Vector.getElem_set, Ne.symm hz, ite_false]

def abstractRound (r : Fin 24) (f : File) : File :=
  step ((run (plan r).core f).write (plan r).constantReg (Spec.Sha3.RC r.val))
    (plan r).iota

theorem abstractRound_state (r : Fin 24) (A : Spec.Sha3.State) (f : File)
    (h : LayoutHolds (plan r).input (logicalState A) f) :
    LayoutHolds (plan r).finish (logicalState (Spec.Sha3.rnd A r.val))
      (abstractRound r f) :=
  plan_iota_state r _ _ (plan_core_state r A f h)

theorem layout_of_regs (layout : Layout) (logical f g : File)
    (h : LayoutHolds layout logical f) (hr : ∀ r, g.regs r = f.regs r) :
    LayoutHolds layout logical g := by
  intro entry i he
  rw [hr]
  exact h entry i he

end VG.Proof.Sha3.AArch64.Scalar.Lazy

end

end

/-! ### `Sha3.AArch64.Scalar.Lazy.Constant`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Lazy.Constant
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64

structure ConstantKeep (d : Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  vec : s'.v = s.v
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem constant_ok (d : Reg) (r : Nat) (s : State) :
    WP isa (.block (constant d r)) s fun s' =>
      ConstantKeep d s s' ∧ s'.gpr d = Sha3.Vector.constantLow (Spec.Sha3.RC r) := by
  by_cases h1 : (Spec.Sha3.RC r).extractLsb' 16 16 = 0 <;>
    by_cases h2 : (Spec.Sha3.RC r).extractLsb' 32 16 = 0 <;>
    by_cases h3 : (Spec.Sha3.RC r).extractLsb' 48 16 = 0
  all_goals
    simp only [constant, h1, h2, h3, ite_true, ite_false,
      List.cons_append, List.nil_append]
    repeat' apply WP.cons rfl
    apply wp_nil
    refine ⟨⟨?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · intro r hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    · simp only [Sha3.Vector.constantLow, h1, h2, h3, ite_true, ite_false,
        Sha3.Vector.movkValue, RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]

end VG.Proof.Sha3.AArch64.Scalar.Lazy.Constant

end

end


@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

def machineFile (s : State) : File :=
  ⟨s.gpr, fun k => vdword (s.v (slotV k)) 0⟩

structure Keep (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → t.v v = s.v v

/-- A complete machine-code round realizes the checked rotated lane layout. -/
theorem round_ok (r : Fin 24) (A : Spec.Sha3.State) (s : State)
    (h : LayoutHolds (plan r).input (logicalState A) (machineFile s)) :
    WP isa (.block (round r)) s fun t =>
      LayoutHolds (plan r).finish (logicalState (Spec.Sha3.rnd A r.val)) (machineFile t) ∧
      Keep s t := by
  let f := machineFile s
  have hrel : VectorFileRel f s := ⟨fun _ => rfl, fun _ _ => rfl⟩
  have hp := plans_shape r
  obtain ⟨t, ht, hrt, hm, hrd, hwr, hsp, hv⟩ :=
    vector_list_ok (plan r).core hp.2.2.2.2.1 f s hrel
  unfold round
  rw [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t, ht, ?_⟩
  rw [WP.block_append_iff]
  refine (Constant.constant_ok (plan r).constantReg r.val t).mono fun u ⟨hk, hu⟩ => ?_
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow_RC r.val r.isLt] at hu
  let f1 := (run (plan r).core f).write (plan r).constantReg (Spec.Sha3.RC r.val)
  have hru : VectorFileRel f1 u := by
    constructor
    · intro q
      by_cases hq : q = (plan r).constantReg
      · subst q
        simpa only [f1, File.write, ite_true] using hu
      · simp only [f1, File.write, ite_eq_right hq]
        exact (hk.gpr q hq).trans (hrt.regs q)
    · intro k hkb
      rw [hk.vec]
      exact hrt.slots k hkb
  obtain ⟨v, hvexec, hrv, hvm, hvrd, hvwr, hvsp, hvvec⟩ :=
    vector_step_ok (plan r).iota hp.2.2.2.2.2 f1 u hru
  refine WP.of_runBlock ⟨v, hvexec, ?_⟩
  refine ⟨?_, ⟨hvm.trans (hk.mem.trans hm), hvrd.trans (hk.rd.trans hrd),
    hvwr.trans (hk.wr.trans hwr), hvsp.trans (hk.sp.trans hsp), ?_⟩⟩
  · exact layout_of_regs _ _ _ _ (abstractRound_state r A f h) hrv.regs
  · intro w h24 h25 h28 h29
    exact (hvvec w h24 h25 h28 h29).trans
      ((congrFun hk.vec w).trans (hv w h24 h25 h28 h29))

end VG.Proof.Sha3.AArch64.Scalar.Lazy

end

end

/-! ### `Sha3.AArch64.Scalar.Lazy.Sequence`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

theorem Keep.refl (s : State) : Keep s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (k : Keep t u) : Keep s u :=
  ⟨k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    fun v a b c d => (k.vec v a b c d).trans (h.vec v a b c d)⟩

def roundPrefix (n : Nat) : List Instr := (List.range n).flatMap roundNat

theorem roundPrefix_ok (n : Nat) (hn : n ≤ 24) (A : Spec.Sha3.State) (s : State)
    (hs : LayoutHolds (stageLayout 0) (logicalState A) (machineFile s)) :
    WP isa (.block (roundPrefix n)) s fun t =>
      LayoutHolds (stageLayout n)
        (logicalState ((List.range n).foldl Spec.Sha3.rnd A)) (machineFile t) ∧ Keep s t := by
  induction n with
  | zero => exact WP.block_nil ⟨hs, Keep.refl s⟩
  | succ n ih =>
    have hlt : n < 24 := by omega_using [hn]
    have hn' : n ≤ 24 := by omega_using [hn]
    have hp : roundPrefix (n+1) = roundPrefix n ++ roundNat n := by
      simp only [roundPrefix, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [hp, WP.block_append_iff]
    refine (ih hn').mono fun t ht => ?_
    have hin : LayoutHolds (plan ⟨n, hlt⟩).input
        (logicalState ((List.range n).foldl Spec.Sha3.rnd A)) (machineFile t) := by
      simpa only [stageLayout, dite_eq_left hlt] using ht.1
    have hr := round_ok ⟨n, hlt⟩ _ t hin
    have hr' : roundNat n = round ⟨n, hlt⟩ := by
      simp only [roundNat, Nat.mod_eq_of_lt hlt]
    rw [hr']
    refine hr.mono fun u hu => ?_
    constructor
    · simpa only [plans_stage, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using hu.1
    · exact ht.2.trans hu.2

theorem normalize_math (A : Spec.Sha3.State) (f : File)
    (h : LayoutHolds (stageLayout 24) (logicalState A) f) :
    ∀ (i : Nat) (hi : i < 25), (run normalize f).regs (laneReg i) = A[i] := by
  intro i hi
  have hc := symRun_correct (environment (logicalState A) f) f
    (symbolicLayout (plan ⟨23, by decide⟩).finish) normalize
    (symbolicLayout_compatible _ _ _ h)
  have he := congrArg (Expr.eval (environment (logicalState A) f)) (normalize_symbolic i hi)
  rw [Expr.rotateNormal_eval, Expr.rotateNormal_eval,
    VG.Bitslice.Anf.rotateRight_zero, VG.Bitslice.Anf.rotateRight_zero, ← hc.1] at he
  exact he.trans (logicalState_lane A i hi)

end VG.Proof.Sha3.AArch64.Scalar.Lazy

end

end


@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

/-- All 24 rounds followed by the one-time canonical lane restoration. -/
theorem core_ok (A : Spec.Sha3.State) (s : State)
    (hs : ∀ (i : Nat) (hi : i < 25), s.gpr (laneReg i) = A[i]) :
    WP isa (.block permutationCore) s fun t =>
      (∀ (i : Nat) (hi : i < 25), t.gpr (laneReg i) = (Spec.Sha3.keccakF A)[i]) ∧ Keep s t := by
  have hl0 : (stageLayout 0).length = 25 := by decide +kernel
  have hcanon : ∀ i < 25, (stageLayout 0).getD i (.x0, 0) = (laneReg i, 0) := by decide +kernel
  have hin : LayoutHolds (stageLayout 0) (logicalState A) (machineFile s) := by
    apply layout_of_at
    intro i hi
    have hi25 : i < 25 := by omega_using [hl0, hi]
    simp only [hcanon i hi25, logicalState_lane _ i hi25,
      VG.Bitslice.Anf.rotateRight_zero]
    exact hs i hi25
  unfold permutationCore
  rw [WP.block_append_iff]
  refine (roundPrefix_ok 24 (by decide) A s hin).mono fun t ht => ?_
  let f := machineFile t
  obtain ⟨u, hu, hru, hm, hrd, hwr, hsp, hv⟩ :=
    vector_list_ok normalize normalize_good f t ⟨fun _ => rfl, fun _ _ => rfl⟩
  refine WP.of_runBlock ⟨u, hu, ?_⟩
  refine ⟨fun i hi => (hru.regs (laneReg i)).trans (normalize_math _ f ht.1 i hi),
    ht.2.trans ⟨hm, hrd, hwr, hsp, hv⟩⟩

theorem core_state_keep (orig : State) (A : Spec.Sha3.State) (s : State)
    (hs : Boundary.CoreState orig A s) :
    WP isa (.block permutationCore) s fun t =>
      Boundary.CoreState orig (Spec.Sha3.keccakF A) t ∧ RoundKeep s t := by
  refine (core_ok A s hs.lanes).mono fun t ⟨hl, hk⟩ => ?_
  refine ⟨?_, ⟨hk.mem, hk.vec⟩⟩
  refine ⟨⟨hk.rd.trans hs.keep.rd, hk.wr.trans hs.keep.wr, hk.sp.trans hs.keep.sp⟩,
    ?_, ?_, ?_, hl⟩
  · simpa only [Boundary.Ptrs, hk.vec .v30 (by decide) (by decide) (by decide) (by decide),
      hk.vec .v31 (by decide) (by decide) (by decide) (by decide)] using hs.ptrs
  · intro i hi
    have hn := savedVec_not_temps i hi
    rw [hk.vec _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.saved i hi
  · intro q hq
    have hn := preservedV_not_temps q hq
    rw [hk.vec _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.vec q hq

theorem core_state (orig : State) (A : Spec.Sha3.State) (s : State)
    (hs : Boundary.CoreState orig A s) :
    WP isa (.block permutationCore) s (Boundary.CoreState orig (Spec.Sha3.keccakF A)) :=
  (core_state_keep orig A s hs).mono fun _ h => h.1

theorem permute_correct (s : State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa permute s t s' ∧ abiPreserved s s' ∧
      VG.Proof.Sha3.permuteAArch64.post s s' :=
  Boundary.wrap_correct (.block permutationCore) (fun orig A s _ hs => core_state orig A s hs)
    s (VG.Proof.Sha3.AArch64.pre_of s hs)

theorem permute_noFrames : permute.noFrames = true := by lit_decide

end VG.Proof.Sha3.AArch64.Scalar.Lazy
