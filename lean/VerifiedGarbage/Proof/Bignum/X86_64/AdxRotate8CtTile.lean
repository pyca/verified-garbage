import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail

/-! ## AdxRotate8CtViews -/
section

/-! Public views used by the tiled reduction's constant-time proof. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

structure TileLayout where
  B : Addr
  Z : Nat
  w : Nat
  e : Nat
  n : Nat
  hZ : slot w 8 ≤ Z
  hw : w = 8 * (n + 1)
  he : hdrBytes + 16 ≤ e
  heZ : e + 8 * (w + 8) ≤ Z
  sep : slot w aN + 8 * w ≤ e - 8

structure TileGood (L : TileLayout) (s : State) : Prop where
  scr : Scr s L.B L.Z
  rdi : s.gpr .rdi = L.B
  rcx : s.gpr .rcx = off L.B L.e
  hdr : ∃ mi, Hdr s.mem L.B L.w mi

structure TileReady (L : TileLayout) (j : Nat) (s : State) : Prop where
  good : TileGood L s
  rbp : s.gpr .rbp = off L.B (slot L.w aN + 64 * j)
  rsi : s.gpr .rsi = off L.B (L.e + 64 * j)

theorem tile_pins : Pins TileGood [.rdi, .rcx] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hs.rdi, ht.rdi]
  · rw [hs.rcx, ht.rcx]

theorem ready_pins (j : Nat) : Pins (fun L s => TileReady L j s) [.rdi, .rcx, .rbp, .rsi] := by
  intro L s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hs.good.rdi, ht.good.rdi]
  · rw [hs.good.rcx, ht.good.rcx]
  · rw [hs.rbp, ht.rbp]
  · rw [hs.rsi, ht.rsi]

theorem begin_fw (L : TileLayout) (s : State) (h : TileGood L s) :
    WP isa AdxRotate8.tileBegin s (TileReady L 0) := by
  obtain ⟨mi, hm⟩ := h.hdr
  refine WP.mono (tileBegin_ok h.scr h.rdi hm L.hZ h.rcx (by have := L.heZ; have := L.hw; omega))
    fun t ⟨_, hp, ho, mt, kt⟩ => ?_
  exact ⟨⟨h.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.rdi,
    (kt.gpr (by decide)).trans h.rcx, mi, mt ▸ hm⟩,
    by simpa only [Nat.mul_zero, Nat.add_zero] using hp,
    by simpa only [Nat.mul_zero, Nat.add_zero] using ho⟩

theorem head_fw (L : TileLayout) (s : State) (h : TileReady L 0 s) :
    WP isa (AdxRotate8.headN 8) s (TileReady L 0) := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have hw := L.hw; have he := L.he; have heZ := L.heZ; have sep := L.sep
  have hp : s.gpr .rbp = off L.B (slot L.w aN) := by simpa only [Nat.mul_zero, Nat.add_zero] using h.rbp
  refine WP.mono (headN_ok (n := 8) (mi := mi) h.good.scr h.good.rdi h.good.rcx hp
    (by omega) (by omega) (by omega) (Nat.le_trans (by decide : 8 * sMinv + 8 ≤ hdrBytes + 16) he) hm.hminv)
    fun t ⟨_, ot, kt⟩ => ?_
  exact ⟨⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, hm.of_outside ot (by omega)⟩,
    (kt.gpr (by decide)).trans h.rbp, (kt.gpr (by decide)).trans h.rsi⟩

theorem clear_fw (L : TileLayout) (s : State) (h : TileReady L 0 s) :
    WP isa (.block AdxRotate8.clearCarry) s (TileReady L 0) := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have he := L.he; have heZ := L.heZ
  refine WP.mono (clearCarry_ok h.good.scr h.good.rcx (by omega) (by omega)) fun t ⟨_, ot, kt⟩ => ?_
  exact ⟨⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, hm.of_outside ot (by omega)⟩,
    (kt.gpr (by decide)).trans h.rbp, (kt.gpr (by decide)).trans h.rsi⟩

theorem next_fw (L : TileLayout) (j : Nat) (s : State) (hj : j < L.n + 1) (h : TileReady L j s) :
    WP isa (.block AdxRotate8.nextBlock) s fun t =>
      TileReady L (j + 1) t ∧ t.zf = some (decide (j + 1 = L.n + 1)) := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have hw := L.hw
  have hp : s.gpr .rbp = off L.B (slot L.w aN + 8 * (8 * j)) := by rw [h.rbp]; congr 1; omega
  have ho : s.gpr .rsi = off L.B (L.e + 8 * (8 * j)) := by rw [h.rsi]; congr 1; omega
  refine WP.mono (nextBlock_ok h.good.scr h.good.rdi hm L.hZ (by omega) hp ho)
    fun t ⟨hp', ho', hz, mt, kt⟩ => ?_
  refine ⟨⟨⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, mt ▸ hm⟩, ?_, ?_⟩, ?_⟩
  · rw [hp']; congr 1; omega
  · rw [ho']; congr 1; omega
  · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega))
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8CtFront -/
section

/-! Constant time of the tile's low block and public block setup. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def AfterFront (L : TileLayout) (s : State) : Prop :=
  TileReady L 1 s ∧ s.zf = some (decide (L.n = 0))

theorem front_ct : RelCT isa (Two TileGood) AdxRotate8.tileFront (Two AfterFront) := by
  unfold AdxRotate8.tileFront
  refine RelCT.seq (two_piece [.rdi, .rcx] tile_pins (by taint_decide) begin_fw) ?_
  refine RelCT.seq (two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) head_fw) ?_
  refine RelCT.seq (two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) clear_fw) ?_
  refine two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) ?_
  intro L s h
  refine WP.mono (next_fw L 0 s (by omega) h) fun t ⟨ht, hz⟩ => ⟨ht, ?_⟩
  rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega))
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8CtMiddle -/
section

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

end

/-! ## AdxRotate8CtTile -/
section

/-! Each tile accesses memory and branches using public pointers and sizes. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem tail_fw (L : TileLayout) (s : State) (h : TileReady L (L.n + 1) s) :
    WP isa AdxRotate8.tailCore s (TileGood L) := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have he := L.he; have heZ := L.heZ; have hw := L.hw
  refine WP.mono (tailCore_ok h.good.scr h.good.rcx h.rsi (by omega) (by omega) (by omega))
    fun t ⟨_, _, ot, kt⟩ => ?_
  exact ⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, hm.of_outside ot (by omega)⟩

theorem tile_ct : RelCT isa (Two TileGood) AdxRotate8.tile (fun _ _ => True) := by
  unfold AdxRotate8.tile AdxRotate8.tileCompute
  refine RelCT.seq (RelCT.seq front_ct (RelCT.seq middles_ct ?_))
    (two_taint [.rdi, .rcx] tile_pins (by taint_decide))
  exact two_piece [.rdi, .rcx, .rbp, .rsi]
    (fun L s t hs ht => ready_pins (L.n + 1) L s t hs ht) (by taint_decide) tail_fw
end VG.Proof.Bignum.X86_64.AdxRotate8

end
