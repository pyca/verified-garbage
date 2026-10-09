import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckCount
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def passHintSum (work out aux : Addr) (c : CheckConstants) (m : Mem) (e : Nat) : Nat → BitVec 32
  | 0 => 0
  | n+1 => passHintSum work out aux c m e n+
      hintSum (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c m e allChecks

/-- The final counter includes exactly the original-input hint outputs from
all completed slices, with no dependence on earlier output writes. -/
theorem finalPass_count (work out aux : Addr) (c : CheckConstants) (d : CheckData)
    {n : Nat} (hn : n≤8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩) {e : Nat} (he : e<4) :
    vword (finalPassData true work out aux c d n).count e=
      vword d.count e+passHintSum work out aux c d.mem e n := by
  induction n with
  | zero => exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [finalPass_step true work out aux c d (by omega) hw,
      checkRun_count _ _ _ _ _ _ allChecks_nodup
        (fun i _ j _ => ha.sep (checkAddr_contains aux (by omega) i) (checkAddr_contains out (by omega) j)) he,
      ih (by omega)]
    have hs : hintSum
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c
        (finalPassData true work out aux c d n).mem e allChecks=
      hintSum
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c d.mem e allChecks := by
      unfold hintSum
      apply congrArg (fun xs : List (BitVec 32) => xs.sum)
      apply List.map_congr_left
      intro i _
      rw [finalPass_read_future true work out aux c d (Nat.le_refl n) (by omega) i,
        finalPass_read_aux true work out aux c d (by omega) (by omega) i ha]
    rw [hs,passHintSum]
    exact BitVec.add_assoc _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired
