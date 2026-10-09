import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCount

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

def hintLaneFailure (m : Mem) (B : BitVec 32) (p a h : Addr) (e : Nat) : Nat → Bool
  | 0 => false
  | j+1 => hintLaneFailure m B p a h e j ||
      decide ((B+(B-1)).toNat≤(hintCtAt (hintRun m B p a h j).mem a j e+(B-1)).toNat)

theorem maskWord_or (a b : Bool) : maskWord a ||| maskWord b=maskWord (a || b) := by
  cases a <;> cases b <;> decide

theorem normMask_mask (x lo width : BitVec 32) :
    normMask x lo width=maskWord (decide (width.toNat≤(x+lo).toNat)) := by
  unfold normMask maskWord
  simp only [decide_eq_true_eq]

theorem hintRun_flag_value (m : Mem) (B : BitVec 32) (p a h : Addr) (j : Nat)
    {e : Nat} (he : e<4) :
    vword (hintRun m B p a h j).flags e=maskWord (hintLaneFailure m B p a h e j) := by
  induction j with
  | zero => simp [hintRun,hintLaneFailure,maskWord,vword]
  | succ j ih =>
    simp only [hintRun,hintStep,laneVector_word _ he,hintLaneFailure]
    rw [ih,normMask_mask,maskWord_or]

theorem hintRun_flag_vector (m : Mem) (B : BitVec 32) (p a h : Addr) (j : Nat) :
    (hintRun m B p a h j).flags=ofVWords
      (maskWord (hintLaneFailure m B p a h 0 j)) (maskWord (hintLaneFailure m B p a h 1 j))
      (maskWord (hintLaneFailure m B p a h 2 j)) (maskWord (hintLaneFailure m B p a h 3 j)) := by
  apply vec_ext; intro e he
  rw [hintRun_flag_value _ _ _ _ _ _ he,VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  have heq : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases heq with rfl | rfl | rfl | rfl <;> rfl

theorem hintRun_finish_flag (m : Mem) (B : BitVec 32) (p a h : Addr) (j : Nat) :
    finishValue (hintRun m B p a h j).flags=
      if hintLaneFailure m B p a h 0 j || hintLaneFailure m B p a h 1 j ||
          hintLaneFailure m B p a h 2 j || hintLaneFailure m B p a h 3 j then 0 else 1 := by
  rw [hintRun_flag_vector,finishValue_masks]

end VG.Proof.MlDsa.AArch64.Optimized.Response
