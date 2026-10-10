import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRun

/-! ## From `PairedFinishSemantic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def FlagMasks (v : BitVec 128) : Prop := ∀e<4,vword v e=0 ∨ vword v e= -1

theorem flag_lanes_zero (v : BitVec 128) :
    (∀e<4,vword v e=0) ↔ vword v 0=0 ∧ vword v 1=0 ∧ vword v 2=0 ∧ vword v 3=0 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩
  · rintro ⟨h0,h1,h2,h3⟩ e he
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;>
      with_reducible assumption

/-- Exact success-bit reduction for the four SIMD rejection-mask lanes. -/
theorem finishValue_accept (v : BitVec 128) (hv : FlagMasks v) :
    finishValue v= @ite _ (∀e<4,vword v e=0) (Classical.propDecidable _) 1 0 := by
  rw [flag_lanes_zero,finishValue]
  rcases hv 0 (by decide) with h0 | h0 <;>
    rcases hv 1 (by decide) with h1 | h1 <;>
    rcases hv 2 (by decide) with h2 | h2 <;>
    rcases hv 3 (by decide) with h3 | h3 <;>
    rw [h0,h1,h2,h3] <;> simp

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedMaskInvariant.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem mask_or_closed {a b : BitVec 32} (ha : a=0 ∨ a= -1) (hb : b=0 ∨ b= -1) :
    a|||b=0 ∨ a|||b= -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem normMask_closed (x lo width : BitVec 32) : normMask x lo width=0 ∨ normMask x lo width= -1 := by
  unfold normMask
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem checkStep_masks (hint : Bool) (raw : BitVec 128) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (hd : FlagMasks d.flags) : FlagMasks (checkStep hint raw out aux c d).flags := by
  intro e he
  rw [checkStep_flag _ _ _ _ _ _ he]
  exact mask_or_closed (hd e he) (normMask_closed _ _ _)

theorem checkRun_masks (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (hd : FlagMasks d.flags) :
    FlagMasks (checkRun hint v out aux c d js).flags := by
  induction js generalizing d with
  | nil => exact hd
  | cons i js ih => exact ih _ (checkStep_masks _ _ _ _ _ _ hd)

theorem finalPass_masks (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) (n : Nat) (hd : FlagMasks d.flags) :
    FlagMasks (finalPassData hint work out aux c d n).flags := by
  induction n with
  | zero => exact hd
  | succ n ih => exact checkRun_masks _ _ _ _ _ _ _ ih

theorem lowPair_masks (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (hd : FlagMasks d.flags) :
    FlagMasks (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags := by
  intro e he
  rw [lowPair_flag _ _ _ _ _ _ _ _ _ he]
  exact mask_or_closed (mask_or_closed (hd e he) (normMask_closed _ _ _)) (normMask_closed _ _ _)

theorem lowRun_masks (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (hd : FlagMasks d.flags) :
    FlagMasks (lowRun g v out aux c d is).flags := by
  induction is generalizing d with
  | nil => exact hd
  | cons i is ih => exact ih _ (lowPair_masks _ _ _ _ _ _ _ _ _ hd)

theorem lowPass_masks (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) (n : Nat) (hd : FlagMasks d.flags) :
    FlagMasks (lowPassData g work out aux c d n).flags := by
  induction n with
  | zero => exact hd
  | succ n ih => exact lowRun_masks _ _ _ _ _ _ _ ih

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
