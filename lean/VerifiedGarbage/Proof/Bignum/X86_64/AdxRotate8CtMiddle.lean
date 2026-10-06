import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CtFront

/-! The number of higher modulus blocks is public. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem middle_fw (L : TileLayout) (i : Nat) (s : State) (hi : i < L.n) (h : TileReady L (i + 1) s) :
    WP isa AdxRotate8.middle s fun t => TileReady L (i + 2) t ∧ t.zf = some (decide (i + 1 = L.n)) := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have he := L.he; have hz := L.heZ; have hw := L.hw; have sep := L.sep
  unfold AdxRotate8.middle
  refine WP.seq (WP.mono (middleBody_ok h.good.scr h.good.rcx h.rbp h.rsi (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun a ⟨_, _, oa, ka⟩ => ?_)
  have ha : TileReady L (i + 1) a := ⟨⟨h.good.scr.congr ka.2.2,
    (ka.gpr (by decide)).trans h.good.rdi, (ka.gpr (by decide)).trans h.good.rcx, mi,
    hm.of_outside (oa.outside (a := L.e - 8) (b := 64 * (i + 2) + 8)
      (by omega) (by omega) (by omega) (by omega)) (by omega)⟩,
    (ka.gpr (by decide)).trans h.rbp, (ka.gpr (by decide)).trans h.rsi⟩
  refine WP.mono (next_fw L (i + 1) a (by omega) ha) fun t ⟨ht, hzt⟩ => ⟨ht, ?_⟩
  rw [hzt]; exact congrArg some (decide_eq_decide.mpr (by omega))

theorem middle_ct : RelCT isa (Two fun p : TileLayout × Nat => fun s =>
    p.2 < p.1.n ∧ TileReady p.1 (p.2 + 1) s) AdxRotate8.middle (fun _ _ => True) := by
  refine two_taint [.rdi, .rcx, .rbp, .rsi] ?_ (by taint_decide)
  intro p s t hs ht
  exact ready_pins (p.2 + 1) p.1 s t hs.2 ht.2

theorem middle_loop_ct : RelCT isa
    (Two fun L s => 0 < L.n ∧ TileReady L 1 s)
    (.loop AdxRotate8.middle .ne) (Two fun L s => TileReady L (L.n + 1) s) := by
  refine two_loop (fun L : TileLayout => L.n) (Φ := fun L i s => TileReady L (i + 1) s)
    middle_ct ?_
  intro L i s hi h
  refine WP.mono (middle_fw L i s hi h) fun t ⟨ht, hz⟩ => ⟨?_, fun _ => ht, fun he => ?_⟩
  · simp only [eval, hz, Option.map_some]
    by_cases he : i + 1 = L.n
    · simp [he]
    · simp [he]; omega
  · simpa only [← he] using ht

theorem middles_ct : RelCT isa (Two AfterFront)
    (.ite .ne (.loop AdxRotate8.middle .ne) (.block [])) (Two fun L s => TileReady L (L.n + 1) s) := by
  refine two_ite (fun L s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine middle_loop_ct.mono ?_ (fun _ _ h => h)
    rintro s t ⟨L, ⟨hs, he⟩, ⟨ht, _⟩⟩
    have hn : 0 < L.n := by
      simp only [eval, hs.2, Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at he
      omega
    exact ⟨L, ⟨hn, hs.1⟩, hn, ht.1⟩
  · apply RelCT.block_nil
    intro s t h
    obtain ⟨L, ⟨hs, he⟩, ⟨ht, _⟩⟩ := h
    have hn : L.n = 0 := by
      simp only [eval, hs.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at he
      exact he
    exact ⟨L, by simpa only [hn, Nat.zero_add] using hs.1, by simpa only [hn, Nat.zero_add] using ht.1⟩
end VG.Proof.Bignum.X86_64.AdxRotate8
