module

public import VerifiedGarbage.Proof.MillerRabin.X86.WordWindows

/-! # The public outer loop consumes all exponent words -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem test_run_count {σ s : State} {base : Addr} {bytes w n : Nat}
    (facts : RoundFacts σ base bytes w) (h : RunState σ base bytes w n s) :
    WP isa (.block [.mov .eax (.mem (sc sK)), .alu .cmp .eax (.imm 0)]) s fun t =>
      RunState σ base bytes w n t ∧ t.zf = some (decide (16 * w - n = 0)) := by
  have upper := facts.upper
  have count := readW_of_w32 (by omega : 16 * w - n < 2 ^ 32) h.count
  refine wp_movS (by rw [h.stage.read_header facts.fit (by decide), count]) fun u U _ =>
    wp_cmpS rfl fun t Ut zt => WP.block_nil ?_
  have hu := h.stage.of_registers U.keeps U.mem
  have ht := hu.of_registers (rs := []) ⟨fun r _ => congrFun Ut.gpr r, Ut.rd, Ut.wr⟩ Ut.mem
  refine ⟨h.of_memory ht (Ut.mem.trans U.mem), ?_⟩
  rw [zt, U.gpr, show BitVec.ofNat 32 (16 * w - n) - 0 = BitVec.ofNat 32 (16 * w - n) from BitVec.sub_zero _]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 16 * w - n < 2 ^ 32)]
  rfl

theorem word_step {σ s : State} {base : Addr} {bytes w i : Nat}
    (facts : RoundFacts σ base bytes w) (hi : i < 2 * w)
    (h : RunState σ base bytes w (16 * w - 8 * (i + 1)) s) :
    WP isa word s fun t => RunState σ base bytes w (16 * w - 8 * i) t ∧
      t.zf = some (decide (i = 0)) := by
  unfold VG.Impl.MillerRabin.X86.word seqs
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (load_run_word facts hi rfl h) ?_)
  rintro u ⟨runU, wordU⟩
  refine WP.seq (WP.mono (word_windows facts hi runU wordU) ?_)
  intro v runV
  refine WP.seq (WP.mono (test_run_count facts runV) ?_)
  rintro t ⟨runT, zero⟩
  refine WP.block_nil ⟨runT, ?_⟩
  rw [zero]
  congr 1
  exact decide_eq_decide.mpr (by omega)

theorem words_loop {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : RunState σ base bytes w 0 s) :
    WP isa (.loop word .ne) s (RunState σ base bytes w (16 * w)) := by
  have lower := facts.lower
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop (N := 2 * w) (by omega)
    (fun j => RunState σ base bytes w (8 * j)) ?_ h) ?_
  · intro j t hj run
    have start : 8 * j = 16 * w - 8 * ((2 * w - j - 1) + 1) := by omega
    rw [start] at run
    refine WP.mono (word_step facts (i := 2 * w - j - 1) (by omega) run) ?_
    rintro u ⟨runU, zero⟩
    refine ⟨?_, ?_⟩
    · simpa only [show 16 * w - 8 * (2 * w - j - 1) = 8 * (j + 1) by omega] using runU
    · rw [zero]
      congr 1
      exact decide_eq_decide.mpr (by omega)
  · intro t run
    simpa only [show 8 * (2 * w) = 16 * w by omega] using run

end VG.Proof.MillerRabin.X86
