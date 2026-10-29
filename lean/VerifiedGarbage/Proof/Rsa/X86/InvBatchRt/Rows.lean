module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Linear
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Reduce
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Shr

import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs
import VerifiedGarbage.Proof.Weierstrass.X86.InvRedMath
/-! # The matrix rows of a batch at a run-time width

`fgRow_ok`: a row of the full-width values, `[a j] = (u f + v g) / 2 ^ 30`;
`abRow_ok`: a row of the coefficients, `[a j] = mred p iv (u a + v b)`.
-/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/InvBatchRt/ShrSigned.lean`, which only this module imported.
section

/-! # The shift right by 30 of a signed value it divides

`shrSigned_ok`: `shr30_ok` for a value divisible by `2 ^ 30`, as the batches' rows give it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Weierstrass.X86.Inv (sext32 shr_word32 wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `shr30` of a signed value divisible by `2 ^ 30`. -/
theorem shrSigned_ok {s : State} (h : Bx L s B Z len N) {dst src : Ref} (hdh : dst.half = 0)
    (hev : nw len % 2 = 0) (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z)
    (hdz : rv (kw len) dst + 4 * (nw len + 1) ≤ Z)
    (sep : rv (kw len) dst + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) dst)
    {y z : Int}
    (hy : (val32 s.mem B (rv (kw len) src) (nw len + 1) : Int) % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) =
      y % ((2 ^ (32 * (nw len + 1)) : Nat) : Int))
    (hy1 : -((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) ≤ y)
    (hy2 : y < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int)) (hz : y = 2 ^ 30 * z) :
    WP isa (shr30 L dst src) s fun u =>
      Bx L u B Z len N ∧
      (val32 u.mem B (rv (kw len) dst) (nw len + 1) : Int) % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) =
        z % ((2 ^ (32 * (nw len + 1)) : Nat) : Int) ∧
      Keeps wordClob s u ∧ Outside B (rv (kw len) dst) (4 * (nw len + 1)) s.mem u.mem := by
  refine WP.mono (shr30_ok h hdh hev hsz hdz sep) fun u ⟨Bu, V, K, O⟩ => ⟨Bu, ?_, K, O⟩
  have Q : 2 ^ (32 * (nw len + 1)) = 2 * (2 ^ (32 * nw len) * 2 ^ 31) := by
    rw [pow32_succ]; omega
  simp only [sext32, Nat.add_sub_cancel, VG.Proof.Weierstrass.X86.Inv.sign32, Q] at V
  rw [Q] at hy ⊢
  exact Divstep.W32.shr_nat (c := 2 ^ 30) (B := 2 ^ 32) rfl rfl
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (by have := val32_lt s.mem B (rv (kw len) src) (nw len + 1); rw [Q] at this; exact this) hy hy1 hy2 hz V

end VG.Proof.Rsa.X86.InvBatchRt
end

end

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- A matrix row of the full-width values: `[a j] = (u f + v g) / 2 ^ 30`, `n + 1` words. -/
theorem fgRow_ok {s : State} (h : Bx L s B Z len N) (he : nw len % 2 = 0) {u v j : Nat}
    (hu4 : u + 4 ≤ 160) (hv4 : v + 4 ≤ 160) (hj : j < 2) {cu cv f g : Int} {p : Nat}
    (hu : s.mem.readW (off B u) 32 = BitVec.ofInt 32 cu) (hv : s.mem.readW (off B v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hf : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      f % 2 ^ (32 * (nw len + 1)))
    (hg : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      g % 2 ^ (32 * (nw len + 1)))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (32 * nw len + 1)) (hdiv : 2 ^ 30 ∣ cu * f + cv * g) :
    WP isa (.seq (linear L u v (a 11) (a 4) (a 5) (a 12) 1) (shr30 L (a j) (a 11))) s fun z =>
      Bx L z B Z len N ∧
      (val32 z.mem B (rv (kw len) (a j)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((cu * f + cv * g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) ∧
      Keeps wordClob s z ∧
      Unch B [(rv (kw len) (a 11), 4 * (nw len + 3)), (rv (kw len) (a 12), 4 * nw len),
        (rv (kw len) (a j), 4 * (nw len + 1))] s.mem z.mem := by
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11; have r12 := rv_a len 12
  have rj := rv_a len j
  have hjb := Nat.mul_le_mul_right (8 * nw len + 8) (show j ≤ 1 by omega)
  rw [Nat.one_mul] at hjb
  refine WP.seq (WP.mono (linear_ok h (e := 1) (tmp := a 12) hu4 hv4 (by decide) rfl rfl rfl
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₁ ⟨H₁, U₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
    Divstep.W32.cong_comb hf hg] at V₁
  have hcomb := Divstep.W32.comb_le huv hfb hgb
  have hpI : (p : Int) < 2 ^ (32 * nw len) * 2 := by
    exact_mod_cast (by simpa only [Nat.pow_succ] using hp)
  have cap : ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) = (2 : Int) ^ (32 * nw len) * 2 ^ 31 := by
    push_cast; rfl
  have lo : -((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) ≤ cu * f + cv * g := by
    rw [cap]; have := neg_abs_le (cu * f + cv * g); linarith
  have hi : cu * f + cv * g < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) := by
    rw [cap]; have := le_abs_self (cu * f + cv * g); linarith
  refine WP.mono (shrSigned_ok H₁ (dst := a j) (src := a 11) rfl he (by omega) (by omega) (by omega)
    (by exact_mod_cast V₁) lo hi (Int.mul_ediv_cancel' hdiv).symm)
    fun z ⟨Hz, V, K, O⟩ => ⟨Hz, by exact_mod_cast V, (K₁.mono (by decide)).trans (K.mono (by decide)), ?_⟩
  intro x hx
  rw [O x (hx (rv (kw len) (a j), 4 * (nw len + 1)) (by simp)), U₁ x (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hx (rv (kw len) (a 11), 4 * (nw len + 3)) (by simp)
    · exact hx (rv (kw len) (a 12), 4 * nw len) (by simp))]

/-- A matrix row of the coefficients: `[a j] = mred p iv (u x + v y)`, `n` words, for `j` 13 or 14. -/
theorem abRow_ok {s : State} (h : Bx L s B Z len N) {u v j : Nat}
    (hu4 : u + 4 ≤ 160) (hv4 : v + 4 ≤ 160) (hj : 13 ≤ j) (hj' : j < 15) {cu cv x y : Int} {p : Nat}
    (hp : 0 < p) (hm : val32 s.mem B (rv (kw len) mo) (nw len) = p)
    (hinv : (p * w32 s.mem B (win + 28) + 1) % 2 ^ 32 = 0)
    (hu : s.mem.readW (off B u) 32 = BitVec.ofInt 32 cu) (hv : s.mem.readW (off B v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hx : (val32 s.mem B (rv (kw len) (a 6)) (nw len) : Int) = x)
    (hy : (val32 s.mem B (rv (kw len) (a 7)) (nw len) : Int) = y) (hxb : |x| ≤ p) (hyb : |y| ≤ p) :
    WP isa (.seq (linear L u v (a 11) (a 6) (a 7) (a 12) 0) (reduce L (a j))) s fun z =>
      Bx L z B Z len N ∧
      (val32 z.mem B (rv (kw len) (a j)) (nw len) : Int) =
        Divstep.W32.mred p (w32 s.mem B (win + 28)) (cu * x + cv * y) ∧
      Keeps wordClob s z ∧
      Unch B [(rv (kw len) (a 11), 4 * (nw len + 2)), (rv (kw len) (a 12), 4 * (nw len + 1)), (signSlot, 4),
        (rv (kw len) (a j), 4 * nw len)] s.mem z.mem := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have e48 : signSlot = 48 := rfl
  have e16 : win = 16 := rfl
  have r2 := rv_a len 2; have r6 := rv_a len 6; have r7 := rv_a len 7; have r11 := rv_a len 11
  have r12 := rv_a len 12
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  refine WP.seq (WP.mono (linear_ok h (e := 0) (tmp := a 12) hu4 hv4 (by decide) rfl rfl rfl
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₁ ⟨H₁, U₁, K₁, V₁⟩ => ?_)
  simp only [Nat.add_zero] at V₁ U₁
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv), hx, hy] at V₁
  have hm₁ : val32 s₁.mem B (rv (kw len) mo) (nw len) = p := by
    rw [Outs.val32 U₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega), hm]
  have iv₁ : w32 s₁.mem B (win + 28) = w32 s.mem B (win + 28) :=
    VG.Proof.Weierstrass.X86.Inv.word_unch U₁ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp only <;> omega) (by omega)
  have bound : |cu * x + cv * y| ≤ 2 ^ 31 * p := by
    have H := Divstep.W32.comb_le huv hxb hyb
    have hp' : (0 : Int) ≤ p := Int.natCast_nonneg _
    omega
  refine WP.mono (reduce_ok H₁ hj (by omega) hp hm₁ (by rw [iv₁]; exact hinv) bound V₁)
    fun z ⟨Hz, U₂, K₂, V₂⟩ => ⟨Hz, by rw [V₂, iv₁], (K₁.mono (by decide)).trans (K₂.mono (by decide)), ?_⟩
  intro q hq
  rw [U₂ q hq]
  apply U₁ q
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hq (rv (kw len) (a 11), 4 * (nw len + 2)) (by simp)
  · have := hq (rv (kw len) (a 12), 4 * (nw len + 1)) (by simp)
    simp only
    omega

end VG.Proof.Rsa.X86.InvBatchRt
