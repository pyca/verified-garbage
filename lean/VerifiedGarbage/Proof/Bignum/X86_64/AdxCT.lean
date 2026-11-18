module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head

/-! ### `Bignum.X86_64.AdxRotate8CT`, which the modules that import this one used -/

section

/-! ### `Bignum.X86_64.AdxRotate8CtTile`, which only this module used -/

section

/-! ## AdxRotate8CtViews -/

@[expose] public section

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

/-- `TileReady`, with the block carry a bit. -/
def TileBit (L : TileLayout) (j : Nat) (s : State) : Prop :=
  TileReady L j s ∧ (word s.mem L.B (L.e - 8)).toNat ≤ 1

theorem bit_pins (j : Nat) : Pins (fun L s => TileBit L j s) [.rdi, .rcx, .rbp, .rsi] :=
  fun L s t hs ht => ready_pins j L s t hs.1 ht.1

theorem begin_fw (L : TileLayout) (s : State) (h : TileGood L s) :
    WP isa AdxRotate8.tileBegin s (TileReady L 0) := by
  obtain ⟨mi, hm⟩ := h.hdr
  refine WP.mono (tileBegin_ok h.scr h.rdi hm L.hZ h.rcx (by have := L.heZ; have := L.hw; omega_arith))
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
    (by omega_using [heZ]) (by omega_using [heZ, sep]) (by omega_using [hw, sep]) (Nat.le_trans (by decide : 8 * sMinv + 8 ≤ hdrBytes + 16) he) hm.hminv)
    fun t ⟨_, ot, kt⟩ => ?_
  exact ⟨⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, hm.of_outside ot (by omega_using [he])⟩,
    (kt.gpr (by decide)).trans h.rbp, (kt.gpr (by decide)).trans h.rsi⟩

theorem clear_fw (L : TileLayout) (s : State) (h : TileReady L 0 s) :
    WP isa (.block AdxRotate8.clearCarry) s (TileBit L 0) := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have he := L.he; have heZ := L.heZ
  refine WP.mono (clearCarry_ok h.good.scr h.good.rcx (by omega_using [he]) (by omega_using [heZ])) fun t ⟨zt, ot, kt⟩ => ?_
  exact ⟨⟨⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, hm.of_outside ot (by omega_using [he])⟩,
    (kt.gpr (by decide)).trans h.rbp, (kt.gpr (by decide)).trans h.rsi⟩, by rw [zt]; decide⟩

theorem next_fw (L : TileLayout) (j : Nat) (s : State) (hj : j < L.n + 1) (h : TileReady L j s) :
    WP isa (.block AdxRotate8.nextBlock) s fun t =>
      TileReady L (j + 1) t ∧ t.zf = some (decide (j + 1 = L.n + 1)) ∧ t.mem = s.mem := by
  obtain ⟨mi, hm⟩ := h.good.hdr
  have hw := L.hw
  have hp : s.gpr .rbp = off L.B (slot L.w aN + 8 * (8 * j)) := by rw [h.rbp]; congr 1; omega_using []
  have ho : s.gpr .rsi = off L.B (L.e + 8 * (8 * j)) := by rw [h.rsi]; congr 1; omega_using []
  refine WP.mono (nextBlock_ok h.good.scr h.good.rdi hm L.hZ (by omega_using [hj, hw]) hp ho)
    fun t ⟨hp', ho', hz, mt, kt⟩ => ?_
  refine ⟨⟨⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, mt ▸ hm⟩, ?_, ?_⟩, ?_, mt⟩
  · rw [hp']; congr 1; omega_using []
  · rw [ho']; congr 1; omega_using []
  · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega_using [hw]))
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8CtFront -/
section

/-! Constant time of the tile's low block and public block setup. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

def AfterFront (L : TileLayout) (s : State) : Prop :=
  TileBit L 1 s ∧ s.zf = some (decide (L.n = 0))

theorem front_ct : RelCT isa (Two TileGood) AdxRotate8.tileFront (Two AfterFront) := by
  unfold AdxRotate8.tileFront
  refine RelCT.seq (two_piece [.rdi, .rcx] tile_pins (by taint_decide) begin_fw) ?_
  refine RelCT.seq (two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) head_fw) ?_
  refine RelCT.seq (two_piece [.rdi, .rcx, .rbp, .rsi] (ready_pins 0) (by taint_decide) clear_fw) ?_
  refine two_piece [.rdi, .rcx, .rbp, .rsi] (bit_pins 0) (by taint_decide) ?_
  intro L s h
  refine WP.mono (next_fw L 0 s (by omega_using []) h.1) fun t ⟨ht, hz, hm⟩ => ⟨⟨ht, hm ▸ h.2⟩, ?_⟩
  rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega_using []))
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8CtMiddle -/
section

/-! The number of higher modulus blocks is public. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem middle_fw (L : TileLayout) (i : Nat) (s : State) (hi : i < L.n) (hb : TileBit L (i + 1) s) :
    WP isa AdxRotate8.middle s fun t => TileBit L (i + 2) t ∧ t.zf = some (decide (i + 1 = L.n)) := by
  have h := hb.1
  obtain ⟨mi, hm⟩ := h.good.hdr
  have he := L.he; have hz := L.heZ; have hw := L.hw; have sep := L.sep
  unfold AdxRotate8.middle
  refine WP.seq (WP.mono (middleBody_ok h.good.scr h.good.rcx h.rbp h.rsi (by omega_using [he])
    (by omega_using [hz]) (by omega_using [hi, hz, hw]) (by omega_using [hi, hz, hw, sep]) (by omega_using []) (by omega_using [hi, hw, sep]) hb.2) fun a ⟨_, ba, oa, ka⟩ => ?_)
  have ha : TileReady L (i + 1) a := ⟨⟨h.good.scr.congr ka.2.2,
    (ka.gpr (by decide)).trans h.good.rdi, (ka.gpr (by decide)).trans h.good.rcx, mi,
    hm.of_outside (oa.outside (a := L.e - 8) (b := 64 * (i + 2) + 8)
      (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [])) (by omega_using [he])⟩,
    (ka.gpr (by decide)).trans h.rbp, (ka.gpr (by decide)).trans h.rsi⟩
  refine WP.mono (next_fw L (i + 1) a (by omega_using [hi]) ha) fun t ⟨ht, hzt, hmt⟩ => ⟨⟨ht, hmt ▸ ba⟩, ?_⟩
  rw [hzt]; exact congrArg some (decide_eq_decide.mpr (by omega_using []))

theorem middle_ct : RelCT isa (Two fun p : TileLayout × Nat => fun s =>
    p.2 < p.1.n ∧ TileBit p.1 (p.2 + 1) s) AdxRotate8.middle (fun _ _ => True) := by
  refine two_taint [.rdi, .rcx, .rbp, .rsi] ?_ (by taint_decide)
  intro p s t hs ht
  exact ready_pins (p.2 + 1) p.1 s t hs.2.1 ht.2.1

theorem middle_loop_ct : RelCT isa
    (Two fun L s => 0 < L.n ∧ TileBit L 1 s)
    (.loop AdxRotate8.middle .ne) (Two fun L s => TileBit L (L.n + 1) s) := by
  refine two_loop (fun L : TileLayout => L.n) (Φ := fun L i s => TileBit L (i + 1) s)
    middle_ct ?_
  intro L i s hi h
  refine WP.mono (middle_fw L i s hi h) fun t ⟨ht, hz⟩ => ⟨?_, fun _ => ht, fun he => ?_⟩
  · simp only [eval, hz, Option.map_some]
    by_cases he : i + 1 = L.n
    · simp [he]
    · simp [he]; omega_using [hi, he]
  · simpa only [← he] using ht

theorem middles_ct : RelCT isa (Two AfterFront)
    (.ite .ne (.loop AdxRotate8.middle .ne) (.block [])) (Two fun L s => TileBit L (L.n + 1) s) := by
  refine two_ite (fun L s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · refine middle_loop_ct.mono ?_ (fun _ _ h => h)
    rintro s t ⟨L, ⟨hs, he⟩, ⟨ht, _⟩⟩
    have hn : 0 < L.n := by
      simp only [eval, hs.2, Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at he
      omega_using [he]
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

theorem tail_fw (L : TileLayout) (s : State) (hb : TileBit L (L.n + 1) s) :
    WP isa AdxRotate8.tailCore s (TileGood L) := by
  have h := hb.1
  obtain ⟨mi, hm⟩ := h.good.hdr
  have he := L.he; have heZ := L.heZ; have hw := L.hw
  refine WP.mono (tailCore_ok h.good.scr h.good.rcx h.rsi (by omega_using [he]) (by omega_using [heZ]) (by omega_using [heZ, hw]) hb.2)
    fun t ⟨_, _, ot, kt⟩ => ?_
  exact ⟨h.good.scr.congr kt.2.2, (kt.gpr (by decide)).trans h.good.rdi,
    (kt.gpr (by decide)).trans h.good.rcx, mi, hm.of_outside ot (by omega_using [he])⟩

theorem tile_ct : RelCT isa (Two TileGood) AdxRotate8.tile (fun _ _ => True) := by
  unfold AdxRotate8.tile AdxRotate8.tileCompute
  refine RelCT.seq (RelCT.seq front_ct (RelCT.seq middles_ct ?_))
    (two_taint [.rdi, .rcx] tile_pins (by taint_decide))
  exact two_piece [.rdi, .rcx, .rbp, .rsi]
    (fun L s t hs ht => ready_pins (L.n + 1) L s t hs.1 ht.1) (by taint_decide) tail_fw
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end

end

/-! ### `Bignum.X86_64.AdxRotate8CtEdges`, which only this module used -/

section

/-! Public header loads establish the pointers used by the edge blocks. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (WP.keep)

theorem setupBases_fw (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block AdxRotate8.setupBases) s fun t => t.gpr .rcx = off L.B (slot L.w aAcc + 16) := by
  obtain ⟨mi, hg, hZ⟩ := h
  have hl := hg.scr.ld (show 8 * sArr aAcc + 8 ≤ L.Z by
    have := hdr_lt_slot L.w 8 (show sArr aAcc < 32 by decide); omega_using [hZ, this])
  unfold AdxRotate8.setupBases
  xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.harr aAcc (by decide), off_add16]

theorem setup_ct : RelCT isa (Two GoodW) (.block AdxRotate8.setup) (fun _ _ => True) := by
  unfold AdxRotate8.setup
  apply VG.RelCT.block_append
  refine RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) setupBases_fw) ?_
  exact two_taint [.rcx] (fun L s t hs ht r hr => by
    have he : r = .rcx := List.mem_singleton.mp hr
    subst r; exact hs.trans ht.symm) (by taint_decide)

def EndW (L : Ws) (s : State) : Prop := GoodW L s ∧ s.gpr .rcx = off L.B (slot L.w aTmp)

theorem finish_ct : RelCT isa (Two EndW) (.block AdxRotate8.finish) (fun _ _ => True) := by
  unfold AdxRotate8.finish
  apply VG.RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun L s => s.gpr .r8 = off L.B (slot L.w aTmp) ∧
    s.gpr .rbp = BitVec.ofNat 64 L.w) [.rdi, .rcx] ?_ (by taint_decide) ?_) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pins_goodW L s t hs.1 ht.1 .rdi (by simp)
    · rw [hs.2, ht.2]
  · intro L s ⟨⟨mi, hg, hZ⟩, hc⟩
    exact WP.mono (finishSetup_ok hg.scr hg.rdi hg.hdr hZ hc) fun _ h => ⟨h.1, h.2.1⟩
  · refine two_taint [.r8, .rbp] ?_ (by taint_decide)
    intro L s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hs.1, ht.1]
    · rw [hs.2, ht.2]
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end

/-! ### `Bignum.X86_64.AdxRotate8CtLoop`, which only this module used -/

section

/-! The outer iteration count and each tile's workspace are public. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

structure W8 where
  ws : Ws
  n : Nat
  hw : ws.w = 8 * n
  hn : 0 < n

def RW (L : W8) (i : Nat) (s : State) : Prop :=
  GoodW L.ws s ∧ s.gpr .rcx = off L.ws.B (slot L.ws.w aAcc + 16 + 64 * i)

def tileLayout (L : W8) (i : Nat) (hi : i < L.n) (hZ : slot L.ws.w 8 ≤ L.ws.Z) : TileLayout :=
  { B := L.ws.B, Z := L.ws.Z, w := L.ws.w, e := slot L.ws.w aAcc + 16 + 64 * i, n := L.n - 1
    hZ := hZ
    hw := by have := L.hw; have := L.hn; omega_arith
    he := by unfold slot; omega_using []
    heZ := by have := L.hw; unfold slot aAcc at *; omega_using [hi, hZ, this]
    sep := by unfold slot aN aAcc; omega_using [] }

theorem outer_body_ct : RelCT isa
    (Two fun p : W8 × Nat => fun s => p.2 < p.1.n ∧ RW p.1 p.2 s)
    AdxRotate8.tile (fun _ _ => True) := by
  apply tile_ct.mono ?_ (fun _ _ h => h)
  rintro s t ⟨⟨L, i⟩, ⟨hi, ⟨⟨mi, hs, hZ⟩, hc⟩⟩, ⟨_, ⟨⟨mj, ht, _⟩, hd⟩⟩⟩
  exact ⟨tileLayout L i hi hZ, ⟨hs.scr, hs.rdi, hc, mi, hs.hdr⟩,
    ⟨ht.scr, ht.rdi, hd, mj, ht.hdr⟩⟩

theorem outer_fw (L : W8) (i : Nat) (s : State) (hi : i < L.n) (h : RW L i s) :
    WP isa AdxRotate8.tile s fun t => isa.eval .ne t = some (decide (i + 1 < L.n)) ∧
      (i + 1 < L.n → RW L (i + 1) t) ∧ (i + 1 = L.n → RW L L.n t) := by
  obtain ⟨⟨mi, hg, hZ⟩, hc⟩ := h
  let T := tileLayout L i hi hZ
  have hw := L.hw
  refine WP.mono (tile_ok (L := L.ws.w + 8) hg.scr hg.rdi hg.hdr hZ T.hw hc
    T.he T.heZ (by omega_using []) T.sep) fun t ⟨_, ct, zt, ot, kt⟩ => ?_
  have hr : RW L (i + 1) t := ⟨⟨mi, ⟨hg.scr.congr kt.2.2,
    (kt.gpr (by decide)).trans hg.rdi, hg.hdr.of_outside ot (by
      have := T.he; change hdrBytes + 16 ≤ slot L.ws.w aAcc + 16 + 64 * i at this; omega_using [this])⟩, hZ⟩,
    by rw [ct]; exact congrArg (off L.ws.B) (by omega_using [])⟩
  refine ⟨?_, fun _ => hr, fun he => he ▸ hr⟩
  simp only [eval, zt, Option.map_some]
  have he : (slot L.ws.w aAcc + 16 + 64 * i + 64 = slot L.ws.w aTmp) ↔ i + 1 = L.n := by
    unfold slot aAcc aTmp; omega_using [hw]
  simp only [he]
  by_cases heq : i + 1 = L.n
  · simp [heq]
  · simp [heq]; omega_using [hi, heq]

theorem outer_ct : RelCT isa (Two fun L s => RW L 0 s)
    (.loop AdxRotate8.tile .ne) (Two fun L s => RW L L.n s) := by
  refine (two_loop (fun L : W8 => L.n) (Φ := RW) outer_body_ct outer_fw).mono ?_ (fun _ _ h => h)
  rintro s t ⟨L, hs, ht⟩
  exact ⟨L, ⟨L.hn, hs⟩, L.hn, ht⟩
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end


/-! Constant time of the complete register-tiled Montgomery reduction. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem redc_ct : RelCT isa (Two fun L : W8 => GoodW L.ws) AdxRotate8.redc
    (Two fun L : W8 => GoodW L.ws) := by
  apply two_post ?_ ?_
  · unfold AdxRotate8.redc
    refine RelCT.seq (two_post (Ψ := fun L s => RW L 0 s) (two_map W8.ws (fun _ _ h => h) setup_ct) ?_) ?_
    · intro L s ⟨mi, hg, hZ⟩
      refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨hc, _, ot, kt⟩ => ?_
      exact ⟨⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
        hg.hdr.of_outside ot (by unfold slot; omega_using [])⟩, hZ⟩,
        by simpa only [Nat.mul_zero, Nat.add_zero] using hc⟩
    refine RelCT.seq outer_ct ?_
    refine two_map W8.ws ?_ finish_ct
    intro L s ⟨hg, hc⟩
    exact ⟨hg, by rw [hc]; congr 1; have := L.hw; unfold slot aAcc aTmp; omega_using [this]⟩
  · intro L s ⟨mi, hg, hZ⟩
    refine WP.mono (redc_ok hg.scr hg.rdi hg.hdr hZ L.hw L.hn) fun t ⟨_, ot, kt⟩ => ?_
    exact ⟨mi, ⟨hg.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg.rdi,
      hg.hdr.of_outside ot (by unfold slot; omega_using [])⟩, hZ⟩
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end

/-!
# Multiword arithmetic on x86-64: the BMI2/ADX multiplication in constant time

As for `montMul_ct`, the pieces that load from the header are checked by the
taint analysis from `rdi`, and what follows them from the registers they set,
which `Two` fixes. The size test, the rows' loop and the end of each row
compare with values from the header, so the branch and the loop are taken
alike in both runs because `Ws` fixes `w` (`two_ite`, `two_loop`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64

/-- Before row `i` of `b`'s multiplication: the window and the bases. -/
def FW (b : Nat) (L : Ws) (i : Nat) (t : State) : Prop :=
  GoodW L t ∧ SizeOk L.w ∧ t.gpr .r8 = off L.B (slot L.w aAcc + 16 + 8 * i) ∧
  t.gpr .r9 = off L.B (slot L.w b) ∧ t.gpr .r10 = off L.B (slot L.w aN) ∧ t.gpr .rbx = BitVec.ofNat 64 L.w

theorem FW.pins {b : Nat} {L : Ws} {i : Nat} {s₁ s₂ : State} (h₁ : FW b L i s₁) (h₂ : FW b L i s₂) :
    ∀ r ∈ [Reg.rdi, .r8, .r9, .r10, .rbx], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact pins_goodW L s₁ s₂ h₁.1 h₂.1 .rdi (by simp)
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

/-- After `rowBase`: `rax` too. -/
def FR (a b : Nat) (p : Ws × Nat) (t : State) : Prop :=
  FW b p.1 p.2 t ∧ t.gpr .rax = off p.1.B (slot p.1.w a) - off p.1.B (slot p.1.w aAcc + 16)

theorem pins_fr (a b : Nat) : Pins (FR a b) [.rdi, .r8, .r9, .r10, .rbx, .rax] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · subst h; rw [h₁.2, h₂.2]

/-- After `finishBases`: the registers of `subMod` and `selectAcc`. -/
def FF (o : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .r8 = off L.B (slot L.w aTmp) ∧ t.gpr .rsi = off L.B (slot L.w aAcc) ∧
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w aN)

theorem pins_ff (o : Nat) : Pins (FF o) [.r12, .r8, .rsi, .rbx, .r10] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

theorem SizeOk.lt {w : Nat} (h : SizeOk w) : w < 2 ^ 31 := by unfold SizeOk at h; omega_arith

/-- A row keeps the bases and the header, and moves the window. -/
theorem row_fw {a b : Nat} (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc)
    (hb2 : b ≠ aTmp) (L : Ws) (j : Nat) (s : State) (hj : j < L.w) (h : FW b L j s) :
    WP isa (row a) s fun s' => isa.eval .ne s' = some (decide (j + 1 < L.w)) ∧
      (j + 1 < L.w → FW b L (j + 1) s') ∧ (j + 1 = L.w → FW b L L.w s') := by
  obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
  have hn := hg.scr.nowrap
  have hg0 : hdrBytes ≤ slot L.w aAcc := by unfold slot; omega_arith
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr hZ ha hb ha1 ha2 hb1 hb2 rfl hj hsz.1 hsz.2.1
    (by have := hsz.lt; omega_arith) h8 h9 h10 hbx) fun s' ⟨_, ho, h8', hz, k⟩ => ?_
  have hg' : GoodW L s' := ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by omega_arith)⟩, hZ⟩
  have hfw : FW b L (j + 1) s' := ⟨hg', hsz, by rw [h8', show slot L.w aAcc + 16 + 8 * j + 8 = slot L.w aAcc + 16 + 8 * (j + 1) by omega_arith], (k.gpr (by decide)).trans h9,
    (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans hbx⟩
  refine ⟨?_, fun _ => hfw, fun he => he ▸ hfw⟩
  simp only [eval, hz, Option.map_some]
  congr 1
  by_cases he : j + 1 = L.w
  · simp [he]
  · simp [he]; omega_arith

/-- The fused multiplication is constant time, given that the taint analysis
checks its header loads from `rdi`. -/
theorem fused_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true) :
    RelCT isa (Two fun L s => GoodW L s ∧ SizeOk L.w) (fused o a b) fun _ _ => True := by
  unfold fused
  -- The bases.
  refine RelCT.seq (two_piece (Ψ := fun L s => FW b L 0 s) [.rdi]
    (fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1) hS fun L s ⟨⟨mi, hg, hZ⟩, hsz⟩ =>
      WP.mono (adxSetup_ok hg.scr hg.rdi hg.hdr hZ hb) fun t ⟨h9, h10, h8, hbx, hm, k⟩ =>
        ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz, h8, h9, h10, hbx⟩) ?_
  -- The windows := 0.
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.w ∧ FW b L 0 s) [.rdi, .r8, .r9, .r10, .rbx]
    (fun L s₁ s₂ h₁ h₂ => h₁.pins h₂) (by taint_decide) fun L s h => ?_) ?_
  · obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
    have hn := hg.scr.nowrap
    refine WP.mono (zeroWin_ok (A := slot L.w aAcc + 16) hg.scr (by rw [h8, Nat.mul_zero, Nat.add_zero]) hbx (by have := hsz.lt; omega_arith)
      (by unfold slot aAcc at *; omega_arith)) fun t ⟨_, ho', k⟩ => ⟨by have := hsz.2.1; omega_arith, ⟨mi, ⟨hg.scr.congr k.2.2,
        (k.gpr (by decide)).trans hg.rdi, hg.hdr.of_outside ho' (by unfold slot hdrBytes; omega_arith)⟩, hZ⟩, hsz,
      (k.gpr (by decide)).trans h8, (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans h10,
      (k.gpr (by decide)).trans hbx⟩
  -- The rows.
  refine RelCT.seq (two_loop (fun L => L.w) (Φ := fun L j s => FW b L j s) (Ψ := fun L s => FW b L L.w s) ?_
    (row_fw ha hb ha1 ha2 hb1 hb2)) ?_
  · unfold row
    refine RelCT.seq (two_piece (Ψ := FR a b) [.rdi] (fun p s₁ s₂ h₁ h₂ => pins_goodW p.1 s₁ s₂ h₁.2.1 h₂.2.1)
      hR fun p s ⟨_, h⟩ => ?_) (two_taint _ (pins_fr a b) (by taint_decide))
    obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
    exact WP.mono (rowBase_ok hg.scr hg.rdi hg.hdr hZ ha) fun t ⟨hax, hm, k⟩ =>
      ⟨⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz,
        (k.gpr (by decide)).trans h8, (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans h10,
        (k.gpr (by decide)).trans hbx⟩, hax⟩
  -- `T - m`, and the selection.
  unfold finish
  refine RelCT.seq (two_piece (Ψ := FF o) [.rdi] (fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1) hF
    fun L s h => ?_) (two_taint _ (pins_ff o) (by taint_decide))
  obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
  exact WP.mono (finishBases_ok hg.scr hg.rdi hg.hdr hZ ho) fun t ⟨h12, h8', hsi, hbx', _, k⟩ =>
    ⟨h12, h8', hsi, hbx', (k.gpr (by decide)).trans h10⟩

end VG.Proof.Bignum.X86_64
