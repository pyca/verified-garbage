module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowPowers
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rsa.X86_64.RpExp

/-! # Recovery windows: one pair of exponent bits -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

namespace RecoveryWindow

theorem top_digit {W j : Nat} (hj : j ≤ 62) :
    W * 2 ^ j % 2 ^ 64 / 2 ^ 62 = W / 2 ^ (62 - j) % 4 := by
  have e1 : 2 ^ 64 = 2 ^ (64 - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
  have e2 : 2 ^ 62 = 2 ^ (62 - j) * 2 ^ j := by rw [← Nat.pow_add]; congr 1; omega
  have e3 : 2 ^ (64 - j) = 2 ^ (62 - j) * 4 := by
    rw [show 4 = 2 ^ 2 from rfl, ← Nat.pow_add]; congr 1; omega
  rw [e1, Nat.mul_mod_mul_right, e2, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos j), e3,
    Nat.mod_mul_right_div_self]

theorem low_digit (e : Nat) {j : Nat} (hj : j ≤ 62) :
    e % 2 ^ 64 / 2 ^ (62 - j) % 4 = e / 2 ^ (62 - j) % 4 := by
  have h : 2 ^ 64 = 2 ^ (62 - j) * 2 ^ (j + 2) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (show 4 ∣ 2 ^ (j + 2) from Nat.pow_dvd_pow (m := 2) (n := j + 2) 2 (by omega))]

theorem prefix_digit (e : Nat) {j : Nat} (hj : j ≤ 62) :
    e / 2 ^ (64 - (j + 2)) = 4 * (e / 2 ^ (64 - j)) + e / 2 ^ (62 - j) % 4 := by
  have h : 2 ^ (64 - j) = 2 ^ (62 - j) * 4 := by
    rw [show 4 = 2 ^ 2 from rfl, ← Nat.pow_add]; congr 1; omega
  rw [h, ← Nat.div_div_eq_div_mul, show 64 - (j + 2) = 62 - j by omega]
  omega

theorem shl2 (x : Nat) : BitVec.ofNat 64 x <<< 2 = BitVec.ofNat 64 (x * 4 % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mod]
  exact Nat.mod_mul_mod _ _ _

/-- The two header writes consume exactly two exponent bits. -/
theorem next_ok {s : State} {B : Addr} {Z w V j : Nat} (hc : Ws s B Z w)
    (hv : word s.mem B (8 * sC2) = BitVec.ofNat 64 V)
    (hj : word s.mem B (8 * sC3) = BitVec.ofNat 64 (64 - 2 * j)) (hj' : j < 32) :
    WP isa (.block windowNext) s fun u => u.zf = some (decide (j + 1 = 32)) ∧
      u.mem = (s.mem.writeW (off B (8 * sC2)) (BitVec.ofNat 64 (V * 4 % 2 ^ 64))).writeW
        (off B (8 * sC3)) (BitVec.ofNat 64 (64 - 2 * (j + 1))) ∧ Keep [.rax] s u := by
  have h256 := hc.h256
  have he : BitVec.ofNat 64 (64 - 2 * j) - 2 = BitVec.ofNat 64 (64 - 2 * (j + 1)) := by
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega : 2 ≤ 64 - 2 * j)]
    congr 1
  have hz : (BitVec.ofNat 64 (64 - 2 * (j + 1)) == 0) = decide (j + 1 = 32) := by
    rw [Bool.beq_eq_decide_eq, decide_eq_decide, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      ofNat64_inj (by omega) (by decide)]
    omega
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.zf = some (decide (j + 1 = 32)) ∧
      u.mem = (s.mem.writeW (off B (8 * sC2)) (BitVec.ofNat 64 (V * 4 % 2 ^ 64))).writeW
        (off B (8 * sC3)) (BitVec.ofNat 64 (64 - 2 * (j + 1)))) (by
    unfold windowNext
    xrun [State.ea, hdr, hc.rdi, hdrOff,
      hc.scr.ld (d := 8 * sC2) (by simp only [sC2, sFn]; omega),
      hc.scr.st (d := 8 * sC2) (by simp only [sC2, sFn]; omega),
      hc.scr.ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega),
      hc.scr.st (d := 8 * sC3) (by simp only [sC3, sFn]; omega), hv,
      (writeW_outside s.mem B (BitVec.ofNat 64 (V * 4 % 2 ^ 64)) (d := 8 * sC2)
        (by simp only [sC2, sFn]; omega)).word
        (d := 8 * sC3) (Or.inr (by simp only [sC2, sC3, sFn]; omega))
        (by simp only [sC3, sFn]; omega), hj, shl2, he, hz]) rfl)
    fun u ⟨⟨hz', hm⟩, hk⟩ => ⟨hz', hm, hk⟩

/-- One window preserves the existing bit-prefix invariant, advancing it by two. -/
theorem body_ok (M : Mont) {s₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el r t g e V j : Nat} (hc : Cst s₀ B Z w minv N el r t)
    (hp : Powers s₀.mem B w N g) (hV : V = e % 2 ^ 64) (hj : j < 32)
    (hi : BitInv s₀ B w N g e V (2 * j) u) :
    WP isa (windowBody M.mm) u fun u' => u'.zf = some (decide (j + 1 = 32)) ∧
      BitInv s₀ B w N g e V (2 * (j + 1)) u' := by
  have hz := hc.hZ16
  have hR := hc.coprime
  have hcu := hc.congr hi.frm (by decide) bit_hs hi.keep (by decide)
  have hpu := hp.congr hi.frm hz (by decide) (by decide) (by decide) (by decide)
  simp only [windowBody, seqs]
  refine WP.seq (WP.mono (select_ok hcu hpu hi.c2 (Nat.mod_lt _ (by decide)))
    fun u₁ ⟨hc₁, f₁, k₁, hlt₁, hx₁⟩ => ?_)
  have hy₁ : wv u₁.mem B (slot w aY) w = wv u.mem B (slot w aY) w :=
    f₁.rg_wv hz (by simp) (by decide) (by decide) (by omega)
  refine WP.seq (WP.mono (mul_ok M hc₁ (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hy₁]; exact hi.ylt))
    fun u₂ ⟨hc₂, f₂, k₂, hlt₂, hy₂⟩ => ?_)
  have hy₂' := mont_sq hR (by rw [hy₁]; exact hi.y) hy₂
  refine WP.seq (WP.mono (mul_ok M hc₂ (a := aY) (b := aY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hlt₂)
    fun u₃ ⟨hc₃, f₃, k₃, hlt₃, hy₃⟩ => ?_)
  have hy₃' := mont_sq hR hy₂' hy₃
  have hx₃ : wv u₃.mem B (slot w aXm) w = wv u₁.mem B (slot w aXm) w :=
    (f₂.rg_trans f₃).rg_wv hz (by simp) (by decide) (by decide) (by omega)
  refine WP.seq (WP.mono (mul_ok M hc₃ (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hx₃]; exact hlt₁))
    fun u₄ ⟨hc₄, f₄, k₄, hlt₄, hy₄⟩ => ?_)
  have hx₃' : wv u₃.mem B (slot w aXm) w % N =
      g ^ (e / 2 ^ (62 - 2 * j) % 4) * 2 ^ (64 * w) % N := by
    rw [hx₃, hx₁, top_digit (by omega), hV, low_digit e (by omega)]
  have hy₄' := mont_mulp hR hy₃' hx₃' hy₄
  have he : 2 * (2 * (e / 2 ^ (64 - 2 * j))) + e / 2 ^ (62 - 2 * j) % 4 =
      e / 2 ^ (64 - 2 * (j + 1)) := by
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, prefix_digit e (by omega)]; omega
  rw [he] at hy₄'
  have ff := f₁.rg_trans f₂ |>.rg_trans f₃ |>.rg_trans f₄
  have hc2₄ : word u₄.mem B (8 * sC2) = BitVec.ofNat 64 (V * 2 ^ (2 * j) % 2 ^ 64) := by
    rw [ff.rg_word (by decide) (by simp)]; exact hi.c2
  have hc3₄ : word u₄.mem B (8 * sC3) = BitVec.ofNat 64 (64 - 2 * j) := by
    rw [ff.rg_word (by decide) (by simp)]; exact hi.c3
  refine WP.mono (next_ok hc₄.ws hc2₄ hc3₄ hj) fun u' ⟨hcond, hm, k₅⟩ => ⟨hcond, ?_⟩
  have f₅ : Frm B (rg w [] [sC2, sC3]) u₄.mem u'.mem := by
    rw [hm]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
      (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
        (by decide))
  refine ⟨((hi.frm.rg_trans ff).rg_trans f₅).rg_mono (by decide) (by decide),
    (((((hi.keep.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide), ?_, ?_, ?_, ?_⟩
  · rw [f₅.rg_wv hz (by decide) (by decide) (by decide) (by omega)]; exact hlt₄
  · rw [f₅.rg_wv hz (by decide) (by decide) (by decide) (by omega)]; exact hy₄'
  · rw [hm, (writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
      (d := 8 * sC2) (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega),
      word_writeW_self]
    congr 1
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.pow_add, ← Nat.mul_assoc, Nat.mod_mul_mod]
  · rw [hm, word_writeW_self]

end RecoveryWindow
end VG.Proof.Rsa.X86_64
