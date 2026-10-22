module

public import VerifiedGarbage.Proof.MillerRabin.X86.Run
public import VerifiedGarbage.Proof.MillerRabin.X86.WordLoad

/-! # Eight windows consume one publicly addressed exponent word -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem load_run_word {σ s : State} {base : Addr} {bytes w i n : Nat}
    (facts : RoundFacts σ base bytes w) (hi : i < 2 * w) (hn : n = 16 * w - 8 * (i + 1))
    (h : RunState σ base bytes w n s) :
    WP isa (.block wordLoad) s fun t => RunState σ base bytes w n t ∧
      t.mem.readW (off base sV) 32 = exponentWord σ base w i := by
  have count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 (8 * (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    change w32 s.mem base sK = _
    rw [h.count, hn, BitVec.toNat_ofNat]
    have := facts.upper
    omega
  refine WP.mono (word_load facts h.stage hi count) ?_
  rintro t ⟨ht, word, frame⟩
  have same (a : Nat) (ha : a < 28) : numAt t.mem base w a = numAt s.mem base w a :=
    header_frame_num h.stage.context.ws.nowrap facts.fit ha (by decide : sV + 4 ≤ 256) frame
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have sameHeader (d : Nat) (hd : d + 4 ≤ 256) (sep : d + 4 ≤ sV ∨ sV + 4 ≤ d) :
      w32 t.mem base d = w32 s.mem base d :=
    congrArg BitVec.toNat (workspace_frame_word h.stage.context.ws.nowrap (Nat.le_trans hd hdrFit)
      (Nat.le_trans (by decide : sV + 4 ≤ 256) hdrFit) sep frame)
  refine ⟨⟨ht, (sameHeader sK (by decide) (by decide)).trans h.count,
    (same 6 (by decide)).trans h.value, (sameHeader sF (by decide) (by decide)).trans h.flag,
    by rw [same 6 (by decide)]; exact h.reduced, (same 8 (by decide)).trans h.minus, ?_⟩,
    BitVec.eq_of_toNat_eq word⟩
  intro i hi
  exact (same (11 + i) (by omega)).trans (h.table i hi)

theorem word_windows {σ s : State} {base : Addr} {bytes w i : Nat}
    (facts : RoundFacts σ base bytes w) (hi : i < 2 * w)
    (h : RunState σ base bytes w (16 * w - 8 * (i + 1)) s)
    (word : s.mem.readW (off base sV) 32 = exponentWord σ base w i) :
    WP isa (.loop win .ne) s (RunState σ base bytes w (16 * w - 8 * i)) := by
  let n0 := 16 * w - 8 * (i + 1)
  let I := fun j t => RunState σ base bytes w (n0 + j) t ∧
    t.mem.readW (off base sV) 32 = shiftedWord σ base w i j
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop (N := 8) (by decide) I ?_ ?_) ?_
  · intro j t hj ⟨run, word⟩
    have nextBound : n0 + j < 16 * w := by dsimp [n0]; omega
    have digit : shiftedWord σ base w i j >>> 28 = BitVec.ofNat 32
        (numAt σ.mem base w 27 / 16 ^ (16 * w - 1 - (n0 + j)) % 16) := by
      rw [show 16 * w - 1 - (n0 + j) = 8 * i + 7 - j by dsimp [n0]; omega]
      exact word_digit hi hj
    refine WP.mono (run_window facts run nextBound word digit) ?_
    rintro u ⟨runU, wordU, zero⟩
    refine ⟨⟨?_, wordU.trans (shifted_word_next σ base w i j)⟩, ?_⟩
    · simpa only [Nat.add_assoc] using runU
    · rw [zero]
      congr 1
      exact decide_eq_decide.mpr (by dsimp [n0]; omega)
  · exact ⟨by simpa only [Nat.add_zero] using h, by simpa only [shiftedWord, Nat.mul_zero, BitVec.shiftLeft_zero] using word⟩
  · rintro t ⟨run, _⟩
    simpa only [show n0 + 8 = 16 * w - 8 * i by dsimp [n0]; omega] using run

end VG.Proof.MillerRabin.X86
