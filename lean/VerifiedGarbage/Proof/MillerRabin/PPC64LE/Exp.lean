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

end VG.Proof.MillerRabin.PPC64LE
