module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Bitslice.Anf

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
    have hlt : n < 24 := by omega
    have hn' : n ≤ 24 := by omega
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
