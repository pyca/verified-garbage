module

public import VerifiedGarbage.Proof.MillerRabin.X86.Run
public import VerifiedGarbage.Proof.MillerRabin.X86.Threshold

/-! # The last three squarings finish the shared Montgomery round -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

abbrev endThreshold (σ : State) (base : Addr) (w : Nat) : Nat :=
  4 - VG.Proof.RsaKeyGen.sigOf (Spec.Rsa.splitTwos (val32 σ.mem base 256 (2 * w) - 1)).1

abbrev finalFlag (σ : State) (base : Addr) (w : Nat) : Bool :=
  (VG.Proof.MillerRabin.Math.msqs (val32 σ.mem base 256 (2 * w)) w (numAt σ.mem base w 10)
    (endThreshold σ base w) 3 (roundRun σ base w (16 * w)) 3).2

theorem final_squares {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (run : RunState σ base bytes w (16 * w) s)
    (tail : σ.mem.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ.mem base 256 (2 * w) - 1)).1 % 64)) :
    WP isa (.seq (.block lowBits) sqLoop) s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sF = (finalFlag σ base w).toNat := by
  refine WP.seq (WP.mono (low_bits facts run.stage) ?_)
  rintro u ⟨hu, count, threshold, frame⟩
  have rSmall : endThreshold σ base w < 2 ^ 31 := by unfold endThreshold; omega
  have fold := tail_fold (Nat.mod_lt _ (by decide : 0 < 64)) tail
  rw [fold, VG.Proof.RsaKeyGen.sigOf_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by unfold endThreshold at rSmall; omega)] at threshold
  have thresholdWord := readW_of_w32 (by unfold endThreshold; omega : endThreshold σ base w < 2 ^ 32) threshold
  have sameArray (a : Nat) (ha : a < 28) : numAt u.mem base w a = numAt s.mem base w a :=
    headers_frame_num run.stage.context.ws.nowrap facts.fit ha
      (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl <;> decide) frame
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have sameF := headers_frame_word (ds := [sR, sQ]) run.stage.context.ws.nowrap
    (Nat.le_trans (by decide : sF + 4 ≤ 256) hdrFit)
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> exact Nat.le_trans (by decide) hdrFit)
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> decide) frame
  have flag : w32 u.mem base sF = (roundRun σ base w (16 * w)).2.toNat :=
    (congrArg BitVec.toNat sameF).trans run.flag
  refine WP.mono (square_loop facts hu (q0 := 3) (r := endThreshold σ base w)
    (F := (roundRun σ base w (16 * w)).2) (by decide) rSmall count thresholdWord flag
    (by rw [sameArray 6 (by decide)]; exact run.reduced)) ?_
  intro t result
  refine ⟨result.stage, ?_⟩
  have value := result.flag
  unfold squareRun at value
  rw [sameArray 8 (by decide), sameArray 6 (by decide), run.minus, run.value] at value
  exact value

end VG.Proof.MillerRabin.X86
