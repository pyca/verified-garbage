module

public import VerifiedGarbage.Proof.MillerRabin.X86.Run
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowCounters

/-! # Start the exponent run from Montgomery one and prepared minus one -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem window_init {σ s : State} {base : Addr} {bytes w : Nat}
    (facts : RoundFacts σ base bytes w) (h : TableState σ base bytes w 14 s) :
    WP isa winInit s (RunState σ base bytes w 0) := by
  unfold winInit seqs
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (h.stage.copy (o := 8) (a := 10) facts.lower facts.upper facts.fit
    (by decide) (by decide) (by decide) (.inr (.inr (.inl rfl))) facts.width) ?_)
  rintro u ⟨minusU, hu, f1, _⟩
  have same1 (a : Nat) (ha : a < 28) (hne : a ≠ 8) : numAt u.mem base w a = numAt s.mem base w a :=
    array_frame_num h.stage.context.ws.nowrap facts.fit ha (by decide) hne f1
  have minus : numAt u.mem base w 8 = numAt σ.mem base w 10 :=
    minusU.trans (h.stage.array_constant facts.lower facts.fit (.inr (.inr (.inl rfl))))
  refine WP.seq (WP.mono (hu.copy (o := 6) (a := 11) facts.lower facts.upper facts.fit
    (by decide) (by decide) (by decide) (.inr (.inl rfl)) facts.width) ?_)
  rintro v ⟨valueV, hv, f2, _⟩
  have same2 (a : Nat) (ha : a < 28) (hne : a ≠ 6) : numAt v.mem base w a = numAt u.mem base w a :=
    array_frame_num hu.context.ws.nowrap facts.fit ha (by decide) hne f2
  have one : numAt v.mem base w 6 = tablePower σ base w 0 :=
    valueV.trans ((same1 11 (by decide) (by decide)).trans (h.table 0 (by decide)))
  refine WP.seq (WP.mono (window_counters facts hv) ?_)
  rintro t ⟨ht, flagT, countT, frame⟩
  have same3 (a : Nat) (ha : a < 28) : numAt t.mem base w a = numAt v.mem base w a :=
    headers_frame_num hv.context.ws.nowrap facts.fit ha
      (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl <;> decide) frame
  have value : numAt t.mem base w 6 = tablePower σ base w 0 := (same3 6 (by decide)).trans one
  refine WP.block_nil ⟨ht, countT, value, flagT, ?_, ?_, ?_⟩
  · rw [value]
    exact facts.one
  · exact (same3 8 (by decide)).trans ((same2 8 (by decide) (by decide)).trans minus)
  · intro i hi
    exact (same3 (11 + i) (by omega)).trans ((same2 (11 + i) (by omega) (by omega)).trans
      ((same1 (11 + i) (by omega) (by omega)).trans (h.table i hi)))

end VG.Proof.MillerRabin.X86
