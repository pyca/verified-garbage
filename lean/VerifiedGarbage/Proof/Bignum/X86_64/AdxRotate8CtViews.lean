import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

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
