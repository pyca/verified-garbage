import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldStage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def runOps (u : Nat) (root : Nat → Nat) (i : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => stageOps u (root i) i ++ runOps u root (i+1) n

theorem runValues_field (i n : Nat) (hin : i+n≤7) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (root : Nat → Nat) {b : Int}
    (hb : 8380417≤b) (hs : 8*b<2147483648) (hv : StageBound v i b)
    (hf : InnerBankField u v w) :
    StageBound (runValues (fun i _ => (negZetaNat (root i) : Int)) i n v) (i+n) b ∧
      InnerBankField u (runValues (fun i _ => (negZetaNat (root i) : Int)) i n v)
        (InverseTraversal.run (runOps u root i n) w) := by
  induction n generalizing i v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hi : i<7 := by omega
    have hp := stageValues_bound ⟨i,hi⟩ v (fun _ => (negZetaNat (root i) : Int)) hb hs hv
    have hfield := stageValues_field ⟨i,hi⟩ v w hu (root i) hb hs hv hf
    have h := ih (i := i+1) (by omega) _ _ hp hfield
    simpa only [runValues,runOps,InverseTraversal.run_append,Nat.add_assoc,Nat.add_comm 1 n] using h

theorem stageBound_zero (v : Vector (BitVec 128) 8) (b : Int) :
    StageBound v 0 b ↔ BankBound v b := by
  simp only [StageBound,BankBound,stageDepth,Nat.reduceLT,ite_true,Nat.mul_zero,
    Nat.not_lt_zero,ite_false,Int.pow_zero,Int.one_mul]

theorem stageBound_seven (v : Vector (BitVec 128) 8) (b : Int) :
    StageBound v 7 b ↔ BankBound v (8*b) := by
  simp only [StageBound,BankBound,stageDepth,Nat.reduceLT,ite_false,Nat.reduceEqDiff,Int.reducePow]

theorem localRoot_index (u : Nat) :
    localRoot u=(fun i _ => (negZetaNat (localIndex u i) : Int)) := rfl

theorem runValues_local (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 33521668) (hf : InnerBankField u v w) :
    BankBound (runValues (localRoot u) 0 7 v) 268173344 ∧
      InnerBankField u (runValues (localRoot u) 0 7 v)
        (InverseTraversal.run (runOps u (localIndex u) 0 7) w) := by
  rw [localRoot_index]
  have h := runValues_field 0 7 (by decide) v w hu (localIndex u) (by decide) (by decide)
    ((stageBound_zero v 33521668).mpr hv) hf
  exact ⟨(stageBound_seven _ _).mp h.1,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
