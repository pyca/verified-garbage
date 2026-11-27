module

import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderSave
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Row
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Bignum.X86_64.AdxCT`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Bignum.X86_64.AdxTiledRawCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTiledRowsCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxRect8RowCT`, which this module and modules that import it used -/

section

/-! Public layout and indices determine all row addresses and loop decisions. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)
open VG.Proof.MlKem.X86_64 (Keep)

structure RowLayout where
  B : Addr
  Z : Nat
  w : Nat
  i : Nat
  j₀ : Nat
  n : Nat
  hZ : slot w 8 ≤ Z
  hw : w < 2^31
  hi : i+8 ≤ w
  hwN : w = j₀+8*n
  hn : 0 < n

/-- Before column block `k`; the header slots `ps` hold the operands' bases. -/
def RowState (ps : List (Nat × Nat)) (L : RowLayout) (k : Nat) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12) = BitVec.ofNat 64 L.i ∧
    word s.mem L.B (8*sFn 13) = BitVec.ofNat 64 (L.j₀+8*k)

/-- At column block `k`, with the loop's state from a start `s₀` whose
memory has the operands' bases. -/
def LoopState (ps : List (Nat × Nat)) (a b : Nat) (L : RowLayout) (k : Nat) (s : State) : Prop :=
  ∃ s₀ mi x cb, Ops s₀.mem L.B L.w ps ∧ StreamInv s₀ L.B L.Z L.w a b L.i L.j₀ k mi x cb s

def AtLoop (ps : List (Nat × Nat)) (a b : Nat) (p : RowLayout × Nat) (s : State) : Prop :=
  p.2 < p.1.n ∧ LoopState ps a b p.1 p.2 s

/-- After `setup`: the operands and the output at the row's first column block. -/
def RowBases (ps : List (Nat × Nat)) (a b : Nat) (L : RowLayout) (s : State) : Prop :=
  (∃ mi, Good s L.B L.Z L.w mi) ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12) = BitVec.ofNat 64 L.i ∧
    word s.mem L.B (8*sFn 13) = BitVec.ofNat 64 L.j₀ ∧ word s.mem L.B carryOffset = 0 ∧
    s.gpr .rcx = off L.B (slot L.w a+8*L.i) ∧
    s.gpr .rbp = off L.B (slot L.w b+8*L.j₀) ∧
    s.gpr .rsi = off L.B (slot L.w aAcc+16+8*(L.i+L.j₀))

def RowRdi (p : RowLayout × Nat) (s : State) : Prop := s.gpr .rdi = p.1.B

theorem setup_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (L : RowLayout) (s : State) (h : RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) :
    WP isa (.block (AdxRect8.setup ca cb)) s (RowBases ps a b L) := by
  obtain ⟨⟨mi,hg,hv,hI,hJ⟩,hc⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at hJ
  refine WP.mono (setup_ok hg.scr hg.rdi hg.hdr L.hZ hv pa pb hI hJ)
    fun t ⟨ca,cb,co,mt,kt⟩ => ?_
  exact ⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,mt ▸ hv,mt ▸ hI,mt ▸ hJ,
    mt ▸ hc,ca,cb,co⟩

theorem load_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State) (h : RowBases ps a b L s) :
    WP isa (.block AdxRotate8.loadCols) s (LoopState ps a b L 0) := by
  obtain ⟨⟨mi,hg⟩,hv,hI,hJ,hc,ca,cb,co⟩ := h
  have hwN := L.hwN; have hn := L.hn
  exact WP.mono (rowLoad_ok (s₀ := s) hg.scr hg.rdi hg.hdr L.hZ L.hi (by omega_using [hwN, hn]) hI hJ (by rw [hc]; rfl)
    ca cb co rfl (Keep.refl _ _)) fun t ht => ⟨s,mi,0,2,hv,ht⟩

theorem tile_fw {ps : List (Nat × Nat)} {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (p : RowLayout × Nat) (s : State) (h : AtLoop ps a b p s) :
    WP isa AdxRect8.streamTile s (RowRdi p) := by
  obtain ⟨hk,s₀,mi,_,_,_,h⟩ := h
  have hi := p.1.hi; have hwN := p.1.hwN; have hZ := p.1.hZ
  have nowrap := h.scr.nowrap
  have hj : p.1.j₀+8*p.2+8 ≤ p.1.w := by omega_using [hk, hwN]
  have ar := tile_ranges hi hj ha ha1 ha2
  have br := tile_ranges hj hi hb hb1 hb2
  have po : s.gpr .rsi = off p.1.B (slot p.1.w aAcc+16+8*(p.1.i+(p.1.j₀+8*p.2))) := by
    rw [h.po]; exact congrArg (off p.1.B) (by unfold rawBase; omega_using [])
  refine WP.mono (streamTile_ok h.scr h.rdi h.pa h.pb po (by omega_using [hZ, ar]) (by omega_using [hZ, br]) (by omega_using [hZ, ar])
    ar.2.2 (by omega_using [br]) (by unfold carryOffset sFn slot hdrBytes aAcc; omega_using []))
    fun t ⟨_,_,_,_,_,_,kt⟩ => (kt.gpr (by decide)).trans h.rdi

theorem loop_pins (ps : List (Nat × Nat)) (a b : Nat) :
    Pins (AtLoop ps a b) [.rdi,.rcx,.rbp,.rsi] := by
  rintro p s t ⟨_,_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.rdi.trans ht.rdi.symm
  · exact hs.pa.trans ht.pa.symm
  · exact hs.pb.trans ht.pb.symm
  · exact hs.po.trans ht.po.symm

theorem row_body_ct {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) :
    RelCT isa (Two (AtLoop ps a b)) AdxRect8.rowStep (fun _ _ => True) := by
  unfold AdxRect8.rowStep
  refine RelCT.seq (two_piece [.rdi,.rcx,.rbp,.rsi] (loop_pins ps a b) (by taint_decide)
      (tile_fw ha hb ha1 ha2 hb1 hb2)) (two_taint [.rdi] ?_ (by taint_decide))
  intro p s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.trans ht.symm

theorem row_fw {ps : List (Nat × Nat)} {a b : Nat}
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (L : RowLayout) (k : Nat) (s : State) (hk : k < L.n) (h : LoopState ps a b L k s) :
    WP isa AdxRect8.rowStep s fun t =>
      isa.eval .ne t = some (decide (k+1 < L.n)) ∧
      (k+1 < L.n → LoopState ps a b L (k+1) t) ∧ (k+1 = L.n → LoopState ps a b L L.n t) := by
  obtain ⟨s₀,mi,x,_,hv,h⟩ := h
  refine WP.mono (streamStep_inv L.hZ L.hw L.hi ha hb ha1 ha2 hb1 hb2 L.hwN hk h) fun t ⟨zt,ht⟩ => ?_
  have post : LoopState ps a b L (k+1) t := ⟨s₀,mi,x,2,hv,ht⟩
  refine ⟨?_,fun _ => post,fun he => he ▸ post⟩
  simp only [eval,zt,Option.map_some]
  by_cases he : k+1 = L.n
  · simp only [he,decide_true,Bool.not_true,show ¬(L.n<L.n) by omega_using [],decide_false]
  · simp only [he,decide_false,Bool.not_false,show k+1<L.n by omega_using [hk, he],decide_true]

theorem end_fw {ps : List (Nat × Nat)} {a b : Nat} (L : RowLayout) (s : State) (h : LoopState ps a b L L.n s) :
    WP isa (.block AdxRotate8.storeCols) s (RowState ps L L.n) := by
  obtain ⟨s₀,mi,_,_,hv,h⟩ := h
  refine WP.mono (rowEnd_ok L.hZ L.hi L.hwN h) fun t ht => ?_
  exact ⟨mi,⟨ht.scr,ht.rdi,ht.hdr⟩,frame_ops hv (by unfold rawBase slot; omega_using []) ht.frame,ht.indexI,ht.indexJ⟩

theorem row_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome = true) :
    RelCT isa (Two fun L s => RowState ps L 0 s ∧ word s.mem L.B carryOffset = 0) (AdxRect8.row ca cb)
      (Two fun L s => RowState ps L L.n s) := by
  unfold AdxRect8.row
  refine RelCT.seq (two_piece [.rdi] ?_ hS (setup_fw pa pb)) ?_
  · rintro L s t ⟨⟨mi,hs,_⟩,_⟩ ⟨⟨mj,ht,_⟩,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_piece [.rsi] ?_ (by taint_decide) load_fw) ?_
  · rintro L s t ⟨_,_,_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,_,_,ht⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm
  refine RelCT.seq ((two_loop (fun L : RowLayout => L.n) (Φ := LoopState ps a b)
    (Ψ := fun L s => LoopState ps a b L L.n s)
    (row_body_ct ha hb ha1 ha2 hb1 hb2) (row_fw ha hb ha1 ha2 hb1 hb2)).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨L,hs,ht⟩
    exact ⟨L,⟨L.hn,hs⟩,L.hn,ht⟩
  refine two_post (two_taint [.rsi] ?_ (by taint_decide)) end_fw
  rintro L s t ⟨_,_,_,_,_,hs⟩ ⟨_,_,_,_,_,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.po.trans ht.po.symm

end VG.Proof.Bignum.X86_64.AdxRect8

end

end

/-! ### `Bignum.X86_64.AdxTiledTailCT`, which only this module used -/

section

/-! The carry-tail branch depends only on the public row number and width. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout rawBase)
open VG.Proof.Bignum.X86_64.AdxHeader (highPad)

def TailReady (L : RowLayout) (s : State) : Prop :=
  (∃ mi, Good s L.B L.Z L.w mi) ∧
    word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i ∧
    s.gpr .rsi=off L.B (rawBase L.w+8*(L.i+L.w))

def TailTested (L : RowLayout) (s : State) : Prop :=
  TailReady L s ∧ s.zf=some (decide (L.i+8=L.w))

def TailBases (L : RowLayout) (s : State) : Prop :=
  s.gpr .rsi=off L.B (rawBase L.w+8*(L.i+L.w+8)) ∧ s.gpr .rdx=off L.B (highPad L.w)

theorem tail_ct : RelCT isa (Two TailReady) AdxTiledProduct.tail (fun _ _ => True) := by
  unfold AdxTiledProduct.tail
  refine RelCT.seq (two_piece (Ψ := TailTested) [.rdi] ?_ (by taint_decide) ?_) ?_
  · rintro L s t ⟨⟨mi,hs⟩,_,_⟩ ⟨⟨mj,ht⟩,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  · rintro L s ⟨⟨mi,hg⟩,idx,ptr⟩
    refine WP.mono (tailTest_ok hg.scr hg.rdi hg.hdr L.hZ L.hw L.hi idx) fun t ⟨zt,mt,kt⟩ => ?_
    exact ⟨⟨⟨mi,hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,mt ▸ hg.hdr⟩,
      mt ▸ idx,(kt.gpr (by decide)).trans ptr⟩,zt⟩
  apply two_ite (Φ := TailTested)
  · intro L s t hs ht
    simp only [eval,hs.2,ht.2]
  · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
  · refine RelCT.seq (two_piece (Ψ := TailBases) [.rdi,.rsi] ?_ (by taint_decide) ?_)
      (two_taint [.rsi,.rdx] ?_ (by taint_decide))
    · rintro L s t ⟨⟨⟨⟨mi,hs⟩,_,ps⟩,_⟩,_⟩ ⟨⟨⟨⟨mj,ht⟩,_,pt⟩,_⟩,_⟩ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.rdi.trans ht.rdi.symm
      · exact ps.trans pt.symm
    · rintro L s ⟨⟨⟨⟨mi,hg⟩,_,ptr⟩,_⟩,_⟩
      exact WP.mono (tailSetup_ok hg.scr hg.rdi hg.hdr L.hZ ptr) fun _ ⟨_,p,e,_,_,_⟩ => ⟨p,e⟩
    · intro L s t hs ht r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end

/-! ## AdxTiledRowCT -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRect8 (RowLayout RowState rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

def RowStart (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=0 ∧ (∃ mi, Good s L.B L.Z L.w mi) ∧ Ops s.mem L.B L.w ps ∧
    word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i

def RowReady (ps : List (Nat × Nat)) (L : RowLayout) (s : State) : Prop :=
  (∃ q, L.w=L.i+8+8*q) ∧ L.j₀=0 ∧ RowState ps L 0 s ∧ word s.mem L.B carryOffset=0

theorem init_fw {ps : List (Nat × Nat)} (L : RowLayout) (s : State) (h : RowStart ps L s) :
    WP isa (.block AdxTiledProduct.rowInit) s (RowReady ps L) := by
  obtain ⟨tail,j0,⟨mi,hg⟩,hv,idx⟩ := h
  refine WP.mono (rowInit_ok hg.scr hg.rdi L.hZ) fun t ⟨c,j,o,k⟩ => ?_
  have f : Frm L.B (ranges L.w) s.mem t.mem := by
    intro x hx
    apply o x
    have := hx (8*sFn 12,32) (by simp [ranges])
    simp only [sFn] at *; omega_using [this]
  have hh : Hdr t.mem L.B L.w mi := frame_hdr hg.hdr f
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.i := by
    rw [o.word (by decide) (by decide)]; exact idx
  exact ⟨tail,j0,⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hh⟩,frame_ops hv f,it,
    by rw [j0]; exact j⟩,c⟩

theorem inner_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : RowLayout) (s : State) (h : RowReady ps L s) :
    WP isa (AdxRect8.row ca cb) s (fun t => TailReady L t ∧ ∃ q, L.w=L.i+8+8*q) := by
  obtain ⟨tail,j0,⟨mi,hg,hv,idx,jdx⟩,carry⟩ := h
  simp only [Nat.mul_zero,Nat.add_zero] at jdx
  refine WP.mono (AdxRect8.row_ok hg.scr hg.rdi hg.hdr hv pa pb L.hZ L.hw L.hi ha hb ha1 ha2 hb1 hb2
    L.hwN L.hn idx jdx (by rw [carry]; rfl)) fun t ht => ?_
  have ptr := ht.endPtr.resolve_left (by have := L.hn; omega_using [this])
  have wn := L.hwN
  rw [j0,Nat.add_zero] at ptr
  rw [j0,Nat.zero_add] at wn
  exact ⟨⟨⟨mi,ht.scr,ht.rdi,ht.hdr⟩,ht.indexI,by simpa only [← wn] using ptr⟩,tail⟩

theorem row_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome=true) :
    RelCT isa (Two (RowStart ps)) (AdxTiledProduct.row ca cb) (fun _ _ => True) := by
  unfold AdxTiledProduct.row
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) init_fw) ?_
  · rintro L s t ⟨_,_,⟨mi,hs⟩,_,_⟩ ⟨_,_,⟨mj,ht⟩,_,_⟩ r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.rdi.trans ht.rdi.symm
  refine RelCT.seq (two_post (two_map id (fun _ _ h => ⟨h.2.2.1,h.2.2.2⟩)
    ((AdxRect8.row_ct pa pb ha hb ha1 ha2 hb1 hb2 hS).mono (fun _ _ h => h) (fun _ _ _ => True.intro)))
    (inner_fw pa pb ha hb ha1 ha2 hb1 hb2)) ?_
  refine RelCT.seq (two_post (two_map id (fun _ _ h => h.1) tail_ct)
    (Ψ := fun L s => s.gpr .rdi=L.B) ?_)
    (two_taint [.rdi] ?_ (by taint_decide))
  · rintro L s ⟨⟨⟨mi,hg⟩,idx,ptr⟩,q,hq⟩
    exact WP.mono (tail_ok hg.scr hg.rdi hg.hdr L.hZ L.hw hq idx ptr)
      fun t ⟨_,_,k⟩ => (k.gpr (by decide)).trans hg.rdi
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r; exact hs.trans ht.symm

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

/-! ## AdxTiledRowsCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

structure Layout where
  B : Addr
  Z : Nat
  w : Nat
  n : Nat
  hZ : slot w 8 ≤ Z
  hw : w<2^31
  hwN : w=8*n
  hn : 0<n

def LoopState (ps : List (Nat × Nat)) (L : Layout) (k : Nat) (s : State) : Prop :=
  ∃ mi, Good s L.B L.Z L.w mi ∧ Ops s.mem L.B L.w ps ∧ word s.mem L.B (8*sFn 12)=BitVec.ofNat 64 (8*k)

def GoodL (L : Layout) (s : State) : Prop := ∃ mi, Good s L.B L.Z L.w mi

/-- `GoodL`, with the header slots `ps` holding the operands' bases. -/
def GoodV (ps : List (Nat × Nat)) (L : Layout) (s : State) : Prop := GoodL L s ∧ Ops s.mem L.B L.w ps

theorem row_loop_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome=true) :
    RelCT isa (Two fun p : Layout × Nat => fun s => p.2<p.1.n ∧ LoopState ps p.1 p.2 s)
      (AdxTiledProduct.row ca cb) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨⟨L,k⟩,⟨hk,mi,gs,vs,is⟩,⟨_,mj,gt,vt,it⟩⟩ es et
  dsimp only at hk
  have wn := L.hwN
  let R : AdxRect8.RowLayout := ⟨L.B,L.Z,L.w,8*k,0,L.n,L.hZ,L.hw,by omega_using [hk, wn],by omega_using [wn],L.hn⟩
  apply row_ct pa pb ha hb ha1 ha2 hb1 hb2 hS s t ts tt s' t' ?_ es et
  exact ⟨R,⟨⟨L.n-k-1,by dsimp [R]; omega_using [hk, wn]⟩,rfl,⟨mi,gs⟩,vs,is⟩,
    ⟨L.n-k-1,by dsimp [R]; omega_using [hk, wn]⟩,rfl,⟨mj,gt⟩,vt,it⟩

theorem row_loop_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : Layout) (k : Nat) (s : State) (hk : k<L.n) (h : LoopState ps L k s) :
    WP isa (AdxTiledProduct.row ca cb) s fun t =>
      isa.eval .ne t=some (decide (k+1<L.n)) ∧
      (k+1<L.n → LoopState ps L (k+1) t) ∧ (k+1=L.n → GoodV ps L t) := by
  obtain ⟨mi,hg,hv,idx⟩ := h
  have wn := L.hwN
  refine WP.mono (row_ok hg.scr hg.rdi hg.hdr hv pa pb L.hZ L.hw L.hwN L.hn
    (by omega_using [hk, wn] : L.w=8*k+8+8*(L.n-k-1)) ha hb ha1 ha2 hb1 hb2 idx)
    fun t ⟨zt,it,_,ht,ft,kt⟩ => ?_
  have good : Good t L.B L.Z L.w mi := ⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,ht⟩
  have hv' := frame_ops hv ft
  refine ⟨?_,fun _ => ⟨mi,good,hv',?_⟩,fun _ => ⟨⟨mi,good⟩,hv'⟩⟩
  · simp only [eval,zt,Option.map_some]
    by_cases he : k+1=L.n
    · simp only [show 8*k+8=L.w by omega_using [wn, he],decide_true,Bool.not_true,
        show ¬(k+1<L.n) by omega_using [he],decide_false]
    · simp only [show ¬(8*k+8=L.w) by omega_using [wn, he],decide_false,Bool.not_false,
        show k+1<L.n by omega_using [hk, he],decide_true]
  · simpa only [show 8*(k+1)=8*k+8 by omega_using []] using it

theorem rows_init_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) s
      (fun t => 0<L.n ∧ LoopState ps L 0 t) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  have hZ := L.hZ
  have iZ : 8*sFn 12+8 ≤ L.Z := by
    have := hdr_lt_slot L.w 8 (show sFn 12<32 by decide); omega_using [hZ, this]
  have nowrap := hg.scr.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem=s.mem.writeW (off L.B (8*sFn 12)) (0 : BitVec 64)) ?_ rfl)
    fun t ⟨mt,kt⟩ => ?_
  · xrun [State.ea,hdr,hg.rdi,hdrOff,hg.scr.st iZ]; rfl
  have ot : Outside L.B (8*sFn 12) 8 s.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have ft : Frm L.B (ranges L.w) s.mem t.mem := by
    intro x hx
    apply ot x
    have := hx (8*sFn 12,32) (by simp [ranges]); omega_using [this]
  exact ⟨L.hn,mi,⟨hg.scr.congr kt.2.2,(kt.gpr (by decide)).trans hg.rdi,frame_hdr hg.hdr ft⟩,
    frame_ops hv ft,by rw [mt,word_writeW_self]; rfl⟩

theorem rows_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) hint).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.rows ca cb) (Two (GoodV ps)) := by
  unfold AdxTiledProduct.rows
  refine RelCT.seq (two_piece [.rdi] ?_ (by taint_decide) rows_init_fw)
    (two_loop (fun L : Layout => L.n) (row_loop_ct pa pb ha hb ha1 ha2 hb1 hb2 hS)
      (row_loop_fw pa pb ha hb ha1 ha2 hb1 hb2))
  rintro L s t ⟨⟨mi,hs⟩,_⟩ ⟨⟨mj,ht⟩,_⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end

end

/-! ### `Bignum.X86_64.AdxHeaderCT`, which this module and modules that import it used -/

section

/-! Saving and restoring header words uses only the public scratch layout. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxHeader
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def Pads (L : Ws) (s : State) : Prop :=
  s.gpr .rdi = L.B ∧ s.gpr .r8 = off L.B (slot L.w aAcc) ∧ s.gpr .r9 = off L.B (highPad L.w)

theorem pads_pins : Pins Pads [.rdi,.r8,.r9] := by
  rintro L s t ⟨ds,ls,hs⟩ ⟨dt,lt,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ds.trans dt.symm
  · exact ls.trans lt.symm
  · exact hs.trans ht.symm

theorem bases_fw (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block AdxHeader.bases) s (Pads L) := by
  obtain ⟨mi,hg,hZ⟩ := h
  exact WP.mono (bases_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨lo,hi,_,kt⟩ =>
    ⟨(kt.gpr (by decide)).trans hg.rdi,lo,hi⟩

theorem save_ct : RelCT isa (Two GoodW) AdxHeader.save (fun _ _ => True) := by
  unfold AdxHeader.save
  exact RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) bases_fw)
    (two_taint [.rdi,.r8,.r9] pads_pins (by taint_decide))

theorem restore_ct : RelCT isa (Two GoodW) AdxHeader.restore (fun _ _ => True) := by
  unfold AdxHeader.restore
  exact RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) bases_fw)
    (two_taint [.rdi,.r8,.r9] pads_pins (by taint_decide))

theorem clear_ct : RelCT isa (Two GoodW) AdxHeader.clear (fun _ _ => True) := by
  unfold AdxHeader.clear
  exact RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) bases_fw)
    (two_taint [.rdi,.r8,.r9] pads_pins (by taint_decide))

end VG.Proof.Bignum.X86_64.AdxHeader

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def Ready (ps : List (Nat × Nat)) (L : Layout) (s : State) : Prop :=
  GoodV ps L s ∧ s.gpr .r8=off L.B (slot L.w aAcc+16) ∧ s.gpr .rbx=BitVec.ofNat 64 L.w

theorem pins_good : Pins GoodL [.rdi] := by
  rintro L s t ⟨mi,hs⟩ ⟨mj,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem pins_goodV (ps : List (Nat × Nat)) : Pins (GoodV ps) [.rdi] :=
  fun L s t hs ht => pins_good L s t hs.1 ht.1

theorem GoodV.of_outside {ps : List (Nat × Nat)} {L : Layout} {s t : State} (h : GoodV ps L s)
    (o : Outside L.B (slot L.w aAcc) (16*L.w+32) s.mem t.mem) (k : VG.Proof.MlKem.X86_64.Keep mmRegs s t) :
    GoodV ps L t := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega_using [])⟩,
    hv.of_outside o (by unfold slot sFn hdrBytes; omega_using [])⟩

/-- `GoodV` after code that changed the borrowed header words, then only the
accumulator. -/
theorem GoodV.of_bare {ps : List (Nat × Nat)} {L : Layout} {s t : State} (h : GoodV ps L s) {m : Mem}
    (o₁ : Outside L.B (8*sFn 12) 32 s.mem m) (o₂ : Outside L.B (slot L.w aAcc) (16*L.w+32) m t.mem)
    (k : VG.Proof.MlKem.X86_64.Keep mmRegs s t) : GoodV ps L t := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,
    (hg.hdr.of_outside_fn o₁ (by unfold sFn; omega_using [])).of_outside o₂ (by unfold slot; omega_using [])⟩,
    (hv.of_outside o₁ (Nat.le_refl _)).of_outside o₂ (by unfold slot sFn hdrBytes; omega_using [])⟩

theorem setup_fw {ps : List (Nat × Nat)} {cb b : Nat} (pb : (cb, b) ∈ ps) (L : Layout) (s : State)
    (h : GoodV ps L s) : WP isa (.block (Adx.setup cb)) s (Ready ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (adxSetupV_ok hg.scr hg.rdi hg.hdr L.hZ (hv.at pb) (hv.lt pb)) fun _ ⟨_,_,p,w,m,k⟩ =>
    ⟨⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,m ▸ hv⟩,p,w⟩

theorem zero_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : Ready ps L s) :
    WP isa Adx.zeroWin8 s (GoodV ps L) := by
  obtain ⟨⟨⟨mi,hg⟩,hv⟩,p,w⟩ := h
  have pads := AdxHeader.pads_bound L.hZ
  have hw := L.hw
  refine WP.mono (zeroWin8_ok hg.scr p w L.hwN L.hn (by omega_using [hw])
    (by unfold AdxHeader.highPad at pads; omega_using [pads])) fun t ⟨_,o,k⟩ => ?_
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega_using [])⟩,
    hv.of_outside o (by unfold slot sFn hdrBytes; omega_using [])⟩

theorem save_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa AdxHeader.save s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  refine WP.mono (AdxHeader.save_ok hg.scr hg.rdi hg.hdr L.hZ) fun t ⟨_,_,f,k⟩ => ?_
  have o : Outside L.B (slot L.w aAcc) (16*L.w+32) s.mem t.mem := by
    intro x hx
    apply f x
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> unfold AdxHeader.highPad at * <;> omega_using [hx]
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega_using [])⟩,
    hv.of_outside o (by unfold slot sFn hdrBytes; omega_using [])⟩

theorem raw_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup cb)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) h₂).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.rawProduct ca cb) (fun _ _ => True) := by
  unfold AdxTiledProduct.rawProduct
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_fw pb)) ?_
  refine RelCT.seq (two_piece [.r8,.rbx] ?_ (by taint_decide) zero_fw) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  have mapGood : ∀ L s, GoodV ps L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨⟨mi,hg⟩,_⟩; exact ⟨mi,hg,L.hZ⟩
  refine RelCT.seq (two_post (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.save_ct) save_fw) ?_
  exact RelCT.seq (rows_ct pa pb ha hb ha1 ha2 hb1 hb2 hR)
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.restore_ct)

theorem rawBare_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup cb)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) h₂).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.rawProductBare ca cb) (fun _ _ => True) := by
  unfold AdxTiledProduct.rawProductBare
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_fw pb)) ?_
  refine RelCT.seq (two_piece [.r8,.rbx] ?_ (by taint_decide) zero_fw) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  have mapGood : ∀ L s, GoodV ps L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨⟨mi,hg⟩,_⟩; exact ⟨mi,hg,L.hZ⟩
  exact RelCT.seq (rows_ct pa pb ha hb ha1 ha2 hb1 hb2 hR)
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.clear_ct)

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem raw_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledProduct.rawProduct ca cb) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawProduct_ok hg.scr hg.rdi hg.hdr hv pa pb L.hZ L.hw L.hwN L.hn ha hb ha1 ha2 hb1 hb2)
    fun _ ⟨_,_,o,k⟩ => GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

theorem rawBare_fw {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledProduct.rawProductBare ca cb) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawProductBare_ok hg.scr hg.rdi hg.hdr hv pa pb L.hZ L.hw L.hwN L.hn ha hb ha1 ha2 hb1 hb2)
    fun _ ⟨_,o₁,_,o₂,k⟩ => GoodV.of_bare ⟨⟨mi,hg⟩,hv⟩ o₁ o₂ k

theorem redc_ct : RelCT isa (Two GoodL) AdxRotate8.redc (Two GoodL) := by
  apply two_post ?_ ?_
  · refine two_map (fun L : Layout => (⟨⟨L.B,L.Z,L.w⟩,L.n,L.hwN,L.hn⟩ : AdxRotate8.W8)) ?_
      (AdxRotate8.redc_ct.mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    rintro L s ⟨mi,hg⟩; exact ⟨mi,hg,L.hZ⟩
  · rintro L s ⟨mi,hg⟩
    exact WP.mono (AdxRotate8.redc_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn) fun _ ⟨_,o,k⟩ =>
      ⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega_using [])⟩

/-- The reduction is constant time, for slots and layouts given by any public data `x`. -/
theorem redcV_ct' {α : Type} {P : α → List (Nat × Nat)} {L : α → Layout} :
    RelCT isa (Two fun x s => GoodV (P x) (L x) s) AdxRotate8.redc (Two fun x s => GoodV (P x) (L x) s) := by
  apply two_post (redc_ct.mono (fun _ _ ⟨x,hs,ht⟩ => ⟨L x,hs.1,ht.1⟩) (fun _ _ _ => True.intro))
  rintro x s ⟨⟨mi,hg⟩,hv⟩
  exact WP.mono (AdxRotate8.redc_ok hg.scr hg.rdi hg.hdr (L x).hZ (L x).hwN (L x).hn) fun _ ⟨_,o,k⟩ =>
    GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

/-- `redcFinish`, for slots and layouts given by any public data `x`. -/
theorem redcFinish_ct {α : Type} {P : α → List (Nat × Nat)} {L : α → Layout} {O : α → Nat} {co : Nat}
    (po : ∀ x, (co, O x) ∈ P x) {h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true) :
    RelCT isa (Two fun x s => GoodV (P x) (L x) s) (AdxTiledProduct.redcFinish co) (fun _ _ => True) := by
  have pins : Pins (fun x s => GoodV (P x) (L x) s) [.rdi] := fun x => pins_goodV (P x) (L x)
  unfold AdxTiledProduct.redcFinish
  refine RelCT.seq redcV_ct' ?_
  refine RelCT.seq (two_piece (Ψ := fun x s => GoodV (P x) (L x) s ∧ s.gpr .r10=off (L x).B (slot (L x).w aN))
    [.rdi] pins (by taint_decide) ?_) ?_
  · rintro x s ⟨⟨mi,hg⟩,hv⟩
    have hZ := (L x).hZ
    have hsrc : readSrc s (.mem (hdr (sArr aN)))=some (off (L x).B (slot (L x).w aN)) := by
      rw [readSrc_word (d := 8*sArr aN) hg.scr (by simp only [State.ea,hdr,hg.rdi,hdrOff])
        (by have := hdr_lt_slot (L x).w 8 (show sArr aN<32 by decide); omega_using [hZ, this]),hg.hdr.harr aN (by decide)]
    exact WP.mono (movMem_ok s (dst := .r10) hsrc) fun _ ⟨p,_,_,k⟩ =>
      ⟨⟨⟨mi,hg.scr.congr k.keep.2.2,(k.keep.gpr (by decide)).trans hg.rdi,k.2.1 ▸ hg.hdr⟩,k.2.1 ▸ hv⟩,p⟩
  unfold Adx.finish8
  refine RelCT.seq (two_piece (Ψ := fun x => FF (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) [.rdi]
    (fun x s t hs ht => pins x s t hs.1 ht.1) hF ?_)
    (two_taint _ (fun x => pins_ff (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) (by taint_decide))
  rintro x s ⟨⟨⟨mi,hg⟩,hv⟩,p⟩
  exact WP.mono (finishBasesV_ok hg.scr hg.rdi hg.hdr (L x).hZ (hv.at (po x)) (hv.lt (po x)))
    fun _ ⟨p12,p8,psi,pbx,_,k⟩ => ⟨p12,p8,psi,pbx,(k.gpr (by decide)).trans p⟩

theorem montMul_ct {ps : List (Nat × Nat)} {co ca cb o a b : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (pb : (cb, b) ∈ ps) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup cb)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.montMul co ca cb) (fun _ _ => True) :=
  RelCT.seq (two_post (raw_ct pa pb ha hb ha1 ha2 hb1 hb2 hS hR) (raw_fw pa pb ha hb ha1 ha2 hb1 hb2))
    (redcFinish_ct (P := fun _ => ps) (L := id) (O := fun _ => o) (fun _ => po) hF)

end VG.Proof.Bignum.X86_64.AdxTiledProduct
