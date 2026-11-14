module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Bitslice.Anf
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
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
