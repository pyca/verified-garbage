module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Window
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The Miller–Rabin round on PPC64LE: the windows of the exponent

`windows_ok`: the windows of `E` (array 27), its words from the top, 16
windows each: `RsaKeyGen.wRun` over all `16 w` windows, from `y = 1` and a
clear flag.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (wRun wWin win_digit shl4_succ)

/-- A 64-bit word of a number of 32-bit digits. -/
theorem word_digit (m : Mem) (B : Addr) (d n i : Nat) (hi : i < n) :
    (word m B (d + 8 * i)).toNat = val32 m B d (2 * n) / 2 ^ (64 * i) % 2 ^ 64 := by
  have e : val32 m B d (2 * n) = val32 m B d (2 * i) + 2 ^ (32 * (2 * i)) *
      (val32 m B (d + 4 * (2 * i)) 2 + 2 ^ (32 * 2) * val32 m B (d + 4 * (2 * i) + 4 * 2) (2 * (n - i - 1))) := by
    rw [← val32_append, ← val32_append, show 2 * i + (2 + 2 * (n - i - 1)) = 2 * n by omega]
  have hL : val32 m B d (2 * i) < 2 ^ (64 * i) := by
    have := val32_lt m B d (2 * i)
    rwa [show 32 * (2 * i) = 64 * i by omega] at this
  rw [word_eq_w32, e, show 32 * (2 * i) = 64 * i by omega, show 4 * (2 * i) = 8 * i by omega,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hL, Nat.zero_add,
    show (2 : Nat) ^ (32 * 2) = 2 ^ 64 by decide, Nat.add_mul_mod_self_left]
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  have h1 := (m.readW (off B (d + 8 * i)) 32).isLt
  have h2 := (m.readW (off B (d + 8 * i + 4)) 32).isLt
  exact (Nat.mod_eq_of_lt (by simp only [w32]; omega)).symm

/-- A window state anchored at `u`, from one anchored earlier. -/
theorem WSt.fresh {rs : List Reg} {s₀ u : State} {B : Addr} {Z w c b : Nat} (h : WSt rs s₀ u B Z w c b) :
    WSt winRegs u u B Z w c b :=
  ⟨h.ctx, h.consts, h.tab, Outs.refl _ _ _, Keep.refl _ _, by decide, fun _ h => h⟩

theorem WSt.join {rs : List Reg} {s₀ u t : State} {B : Addr} {Z w c b : Nat} (h : WSt rs s₀ u B Z w c b)
    (h' : WSt winRegs u t B Z w c b) : WSt rs s₀ t B Z w c b := by
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega
  exact h.stepW h'.outs h'.keep (fun _ h => h) (Outs.w32_0 h'.outs (fun r hr => by
    simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slot_lt (by decide)) hn)

/-- The registers the windows write. -/
def expRegs : List Reg := winRegs ++ [.r25, .r26, .r27]

/-- The state of the windows after the top `j` of the `16 w` windows. -/
structure ExpAt (s₀ t : State) (B : Addr) (Z w c b j : Nat) : Prop where
  ws : WSt expRegs s₀ t B Z w c b
  y : arr t.mem B w aY = (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) j).1 * 2 ^ (64 * w) % c
  lt : (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) j).1 < c
  p : t.gpr .r23 = mask (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) j).2

theorem off_sub8 (B : Addr) (y : Nat) : off B (y + 8) - BitVec.ofNat 64 8 = off B y := by
  rw [← off_add, BitVec.add_sub_cancel]

/-- The inner loop: the 16 windows of the word `V`, from window `16 k`. -/
theorem inner_ok {s₀ u : State} {B : Addr} {Z w c b k : Nat} {V : BitVec 64} (hk : k < w)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hV : V.toNat = VG.Proof.RsaKeyGen.mrE c / 2 ^ (64 * (w - 1 - k)) % 2 ^ 64)
    (h : ExpAt s₀ u B Z w c b (16 * k)) (h24 : u.gpr .r24 = V) (h27 : u.gpr .r27 = BitVec.ofNat 64 16) :
    WP isa (.loop (.seq window (.block [.subi .r27 .r27 1])) (.nonzero .d .r27)) u fun t =>
      ExpAt s₀ t B Z w c b (16 * (k + 1)) ∧ t.gpr .r25 = u.gpr .r25 ∧ t.gpr .r26 = u.gpr .r26 := by
  let I : Nat → State → Prop := fun i t => ExpAt s₀ t B Z w c b (16 * k + i) ∧ t.gpr .r24 = V <<< (4 * i) ∧
    t.gpr .r25 = u.gpr .r25 ∧ t.gpr .r26 = u.gpr .r26
  refine WP.mono (wp_countdown (body := .seq window (.block [.subi .r27 .r27 1])) (cnt := .r27) (N := 16)
    (by decide) (by decide) I (fun i hi t ⟨ht, t24, t25, t26⟩ _ => ?_) ⟨by simpa using h, by simp [h24], rfl, rfl⟩ h27)
    fun t ⟨ht, _, t25, t26⟩ => ⟨by rw [show 16 * (k + 1) = 16 * k + 16 by omega]; exact ht, t25, t26⟩
  refine WP.seq (WP.mono (window_ok ht.ws.fresh hc3 hodd ht.y ht.p t24) fun x ⟨hx, xy, xl, x23, x24⟩ => ?_)
  have hd : ((V <<< (4 * i)) >>> 60).toNat =
      VG.Proof.RsaKeyGen.mrE c / 16 ^ (16 * w - 1 - (16 * k + i)) % 16 := by
    rw [win_digit (k := w - k) (by rw [hV, show w - k - 1 = w - 1 - k by omega]) hi]
    rw [show 16 * (w - k - 1) + (15 - i) = 16 * w - 1 - (16 * k + i) by omega]
  have hrun : wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) (16 * k + i + 1) =
      wWin c b ((V <<< (4 * i)) >>> 60).toNat
        ((wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) (16 * k + i)).1,
          (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) (16 * k + i)).2) := by
    rw [hd, wRun]
  have hsub : WP isa (.block [.subi .r27 .r27 1]) x fun z =>
      (z.gpr .r27 = x.gpr .r27 - BitVec.ofNat 64 1 ∧ z.mem = x.mem) ∧ Keep [.r27] x z := by
    refine WP.keep _ ?_ (by decide)
    prun
  have hj := ht.ws.join hx
  refine WP.mono hsub fun z ⟨⟨z27, zm⟩, kz⟩ => ⟨⟨⟨hj.step (by rw [zm]; exact Outs.refl _ _ _) kz (by decide) (by rw [zm]),
    ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [zm, xy, ← hrun]; rfl
  · rw [← hrun] at xl; exact xl
  · rw [kz.gpr .r23 (by decide), x23, ← hrun]; rfl
  · rw [kz.gpr .r24 (by decide), x24, shl4_succ]
  · rw [kz.gpr .r25 (by decide), hx.keep.gpr .r25 (by decide), t25]
  · rw [kz.gpr .r26 (by decide), hx.keep.gpr .r26 (by decide), t26]
  · rw [z27, hx.keep.gpr .r27 (by decide)]

theorem shl3_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem shr1_ofNat (w : Nat) (hw : w ≤ 128) : BitVec.ofNat 64 (2 * w) >>> 1 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The windows of `E`: `RsaKeyGen.wRun` over all `16 w` windows, from
`y = R mod c` (`1`) and a clear flag. -/
theorem windows_ok {s : State} {B : Addr} {Z w c b : Nat} (h : WSt expRegs s s B Z w c b) (hc3 : 3 ≤ c)
    (hodd : c % 2 = 1) (hy : arr s.mem B w aY = 2 ^ (64 * w) % c) :
    WP isa windows s fun t => ExpAt s t B Z w c b (16 * w) := by
  have hw := h.ctx.hw
  have hw' := h.ctx.hw'
  have hZ := h.ctx.hZ
  have hnw := h.ctx.hs.nowrap
  have hE := slot_lt (w := w) (show aE < 28 by decide)
  unfold windows
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.li .r23 0, .lsr .d .r26 .r11 1]) s fun t =>
      (t.gpr .r23 = mask false ∧ t.gpr .r26 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.r23, .r26] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h.ctx.h11, shr1_ofNat w hw']
    rfl
  refine WP.mono h1 fun t₁ ⟨⟨a23, a26, m1⟩, k1⟩ => ?_
  have f1 := h.step (by rw [m1]; exact Outs.refl _ _ _) k1 (by decide) (by rw [m1])
  rw [WP.block_append_iff]
  refine WP.mono (f1.ctx.base (rd := .r25) (by decide) (by decide) aE) fun t₂ ⟨⟨a25, m2⟩, k2⟩ => ?_
  have f2 := f1.step (by rw [m2]; exact Outs.refl _ _ _) k2 (by decide) (by rw [m2])
  have h3 : WP isa (.block [.lsl .r0 .r26 3, .add .r25 .r25 .r0]) t₂ fun t =>
      (t.gpr .r25 = off B (slot w aE + 8 * w) ∧ t.mem = t₂.mem) ∧ Keep [.r0, .r25] t₂ t := by
    refine WP.keep _ ?_ (by decide)
    prun [k2.gpr .r26 (by decide), a26, a25, shl3_ofNat w, off_add]
  refine WP.mono h3 fun t₃ ⟨⟨b25, m3⟩, k3⟩ => ?_
  have f3 := f2.step (by rw [m3]; exact Outs.refl _ _ _) k3 (by decide) (by rw [m3])
  have e0 : ExpAt s t₃ B Z w c b (16 * 0) :=
    ⟨f3, by rw [m3, m2, m1, hy]; simp [wRun], by simp [wRun]; omega,
      by rw [k3.gpr .r23 (by decide), k2.gpr .r23 (by decide), a23]; rfl⟩
  have c26 : t₃.gpr .r26 = BitVec.ofNat 64 w := by rw [k3.gpr .r26 (by decide), k2.gpr .r26 (by decide), a26]
  let I : Nat → State → Prop := fun k t => ExpAt s t B Z w c b (16 * k) ∧
    t.gpr .r25 = off B (slot w aE + 8 * (w - k))
  refine WP.mono (wp_countdown (cnt := .r26) (N := w) (by omega) (by omega) I
    (fun k hk t ⟨ht, t25⟩ _ => ?_) ⟨e0, by rw [b25, Nat.sub_zero]⟩ c26) fun t ⟨ht, _⟩ => ht
  -- the next word
  have hy8 : slot w aE + 8 * (w - k) = (slot w aE + 8 * (w - 1 - k)) + 8 := by omega
  have hld : WP isa (.block [.subi .r25 .r25 8, .load .d .r24 .r25 0, .li .r27 16]) t fun u =>
      (u.gpr .r25 = off B (slot w aE + 8 * (w - 1 - k)) ∧
        u.gpr .r24 = word t.mem B (slot w aE + 8 * (w - 1 - k)) ∧ u.gpr .r27 = BitVec.ofNat 64 16 ∧
        u.mem = t.mem) ∧ Keep [.r24, .r25, .r27] t u := by
    refine WP.keep _ ?_ (by decide)
    prun [t25, hy8, off_sub8, (ht.ws.ctx.hs).ld (show slot w aE + 8 * (w - 1 - k) + 8 ≤ Z by omega)]
  refine WP.seq (WP.mono hld fun u ⟨⟨u25, u24, u27, um⟩, ku⟩ => ?_)
  have eu : ExpAt s u B Z w c b (16 * k) :=
    ⟨ht.ws.step (by rw [um]; exact Outs.refl _ _ _) ku (by decide) (by rw [um]), by rw [um]; exact ht.y, ht.lt,
      by rw [ku.gpr .r23 (by decide)]; exact ht.p⟩
  have hV : (word t.mem B (slot w aE + 8 * (w - 1 - k))).toNat =
      VG.Proof.RsaKeyGen.mrE c / 2 ^ (64 * (w - 1 - k)) % 2 ^ 64 := by
    rw [word_digit _ _ _ _ _ (show w - 1 - k < w by omega)]
    rw [show val32 t.mem B (slot w aE) (2 * w) = arr t.mem B w aE from rfl, ht.ws.consts.e]
  refine WP.seq (WP.mono (inner_ok hk hc3 hodd hV eu u24 u27) fun x ⟨ex, x25, x26⟩ => ?_)
  have hsub : WP isa (.block [.subi .r26 .r26 1]) x fun z =>
      (z.gpr .r26 = x.gpr .r26 - BitVec.ofNat 64 1 ∧ z.mem = x.mem) ∧ Keep [.r26] x z := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hsub fun z ⟨⟨z26, zm⟩, kz⟩ => ⟨⟨⟨ex.ws.step (by rw [zm]; exact Outs.refl _ _ _) kz (by decide)
    (by rw [zm]), by rw [zm]; exact ex.y, ex.lt, by rw [kz.gpr .r23 (by decide)]; exact ex.p⟩, ?_⟩, ?_⟩
  · rw [kz.gpr .r25 (by decide), x25, u25, show w - 1 - k = w - (k + 1) by omega]
  · rw [z26, x26, ku.gpr .r26 (by decide)]

end VG.Proof.MillerRabin.PPC64LE
