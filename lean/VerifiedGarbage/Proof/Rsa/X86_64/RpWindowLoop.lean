module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowStep
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpHalf
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.X86_64.RpExp

/-! # Recovery windows: the padded exponent and the complete exponentiation -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

namespace RecoveryWindow

/-- A word. -/
theorem word_ok (M : Mont) {t₀ u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g k : Nat}
    (hc : Cst t₀ B Z w minv N el r t) (hp : Powers t₀.mem B w N g) (_hGlt : wv t₀.mem B (slot w aG) w < N)
    (_hG : wv t₀.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) (hk : k < w + (el + 7) / 8)
    (hI : WordInv t₀ B w N g r (w + (el + 7) / 8) k u) :
    WP isa (.seq (.block wordHead) (.seq (.loop (windowBody M.mm) .ne) (.block wordNext))) u fun u' =>
      u'.zf = some (decide (k + 1 = w + (el + 7) / 8)) ∧ WordInv t₀ B w N g r (w + (el + 7) / 8) (k + 1) u' := by
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw2 := hc.ws.w2
  obtain ⟨Bw, hBw⟩ : ∃ Bw, w + (el + 7) / 8 = Bw := ⟨_, rfl⟩
  have hm := hc.hm
  rw [hBw] at hk hI hm ⊢
  have hBw2 : Bw ≤ 2 * (w + 2) := by omega_using [he2, hBw]
  have hcu : Cst u B Z w minv N el r t := hc.congr hI.frm (by decide) word_hs hI.keep (by decide)
  obtain ⟨i, hi⟩ : ∃ i, Bw - k = i + 1 := ⟨Bw - k - 1, by omega_using [hk]⟩
  have hc1 := hI.c1
  rw [hi] at hc1
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by simp only [slot, hdrBytes, aM]; omega_using []
  have hZ := hcu.ws.hZ
  refine WP.seq (WP.mono (wordHead_ok hcu.ws hc1 (by omega_using [hBw2, hi, sM, eM1, hZ])
      (by omega_using [hw2, hBw2, hi])) fun u₁ ⟨m₁, k₁⟩ => ?_)
  -- The word.
  have hW : (word u.mem B (slot w aM + 8 * i)).toNat = r / 2 ^ (64 * i) % 2 ^ 64 := by
    have := word_of_wv u.mem B (slot w aM) Bw (q := i) (by omega_using [hi])
    have hmu := hcu.hm
    rw [hBw] at hmu
    rw [hmu] at this
    exact this
  have hf₁ : Frm B (rg w [] [sC2, sC3]) u.mem u₁.mem := by
    rw [m₁]
    exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega_using [])) [] [sC2, sC3] (by decide)).trans
      (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega_using [])) [] [sC2, sC3] (by decide))
  have hc₁ := hcu.congr hf₁ (by decide) (by decide) k₁ (by decide)
  have hGu : wv u₁.mem B (slot w aG) w = wv t₀.mem B (slot w aG) w := by
    rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []),
      hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using [])]
  -- The bits of the word.
  have hpow : r / 2 ^ (64 * i) / 2 ^ (64 - 0) = r / 2 ^ (64 * (Bw - k)) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hi, Nat.sub_zero, Nat.mul_succ]
  have hW' : word u.mem B (slot w aM + 8 * i) = BitVec.ofNat 64 (r / 2 ^ (64 * i) % 2 ^ 64 * 2 ^ 0 % 2 ^ 64) := by
    rw [← hW, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hB0 : BitInv u₁ B w N g (r / 2 ^ (64 * i)) (r / 2 ^ (64 * i) % 2 ^ 64) 0 u₁ := by
    refine ⟨Frm.refl _ _ _, Keep.refl _ _, ?_, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using [])]; exact hI.ylt
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []), hpow]; exact hI.y
    · rw [m₁, (writeW_outside _ B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega_using [])).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega_using [])) (by simp only [sC2, sFn]; omega_using []), word_writeW_self, hW']
    · rw [m₁, word_writeW_self]
  refine WP.seq (wp_upto (a := 0) (N := 32) (by decide) (fun j v => BitInv u₁ B w N g (r / 2 ^ (64 * i)) (r / 2 ^ (64 * i) % 2 ^ 64) (2 * j) v)
    (fun j _ hj v hv => body_ok M hc₁ (hp.congr (hI.frm.rg_trans hf₁) hZ16 (by decide) (by decide) (by decide) (by decide)) rfl hj hv)
    (fun v hv => ?_) hB0)
  have hc₂ := hc₁.congr hv.frm (by decide) bit_hs hv.keep (by decide)
  have hc1₂ : word v.mem B (8 * sC1) = BitVec.ofNat 64 (i + 1) := by
    rw [hv.frm.rg_word (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact hc1
  refine WP.mono (ctrDec_ok hc₂.ws (i := sC1) (by decide) (by decide) hc1₂ (by omega_using []) (by omega_using [hw2, hBw2, hi]))
    fun u' ⟨hz, m₃, k₃⟩ => ⟨by rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega_using [hi]), ?_⟩
  have hf₃ : Frm B (rg w [] [sC1]) v.mem u'.mem := by
    rw [m₃]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega_using [])) _ _
      (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((hI.frm.rg_trans hf₁).rg_trans hv.frm).rg_trans hf₃).rg_mono (by decide) (by decide)
  · exact (((hI.keep.trans k₁).trans hv.keep).trans k₃).mono (by decide)
  · rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using [])]; exact hv.ylt
  · rw [hf₃.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []), show Bw - (k + 1) = i by omega_using [hi]]
    have := hv.y
    rwa [Nat.sub_self, Nat.pow_zero, Nat.div_one] at this
  · rw [m₃, word_writeW_self, show Bw - (k + 1) = i by omega_using [hi], Nat.add_sub_cancel]

/-! ## The exponentiation -/

/-- `expLoop`: `Y ≡ g^r R`, from `Y = R mod n` and `G ≡ g R`. -/
theorem loop_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g : Nat}
    (hc : Cst s B Z w minv N el r t) (hp : Powers s.mem B w N g) (hGlt : wv s.mem B (slot w aG) w < N)
    (hG : wv s.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % N) :
    WP isa (windowLoop M.mm) s fun u => Frm B (rg w [aAcc, aTmp, aXm, aY] [sC1, sC2, sC3]) s.mem u.mem ∧
      Keep mmRegs s u ∧ wv u.mem B (slot w aY) w < N ∧
      wv u.mem B (slot w aY) w % N = g ^ r * 2 ^ (64 * w) % N := by
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hN : 0 < N := by have := hc.n1; omega_using [this]
  unfold windowLoop expInit
  refine WP.seq (WP.mono (Q := fun (u : State) => u.mem = s.mem.writeW (off B (8 * sC1))
      (BitVec.ofNat 64 (w + (el + 7) / 8)) ∧ Keep mmRegs s u)
    (WP.block_append_iff.mpr (WP.mono (bw_ok hc.ws hc.hel (by omega_using [he2, hw2])) fun s₁ ⟨hax, m₁, k₁⟩ => ?_))
    fun s₁ ⟨m₁, k₁⟩ => ?_)
  · have hs₁ := hc.ws.scr.congr k₁.2.2
    have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hc.ws.rdi
    refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off B (8 * sC1))
        (BitVec.ofNat 64 (w + (el + 7) / 8))) (by
      xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega_using [h256]), hax, m₁])
      rfl) fun u ⟨mu, k₂⟩ => ⟨mu, (k₁.trans k₂).mono (by decide)⟩
  have hf₁ : Frm B (rg w [] [sC1]) s.mem s₁.mem := by
    rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega_using [])) _ _
      (List.mem_singleton_self _)
  have hr : r < 2 ^ (64 * (w + (el + 7) / 8)) := hc.hm ▸ wv_lt _ _ _ _
  have h0 : WordInv s B w N g r (w + (el + 7) / 8) 0 s₁ := by
    refine ⟨hf₁.rg_mono (by decide) (by decide), k₁, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []), hY]; exact Nat.mod_lt _ hN
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []), hY, Nat.sub_zero,
        Nat.div_eq_of_lt hr, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
    · rw [m₁, word_writeW_self, Nat.sub_zero]
  refine wp_upto (a := 0) (N := w + (el + 7) / 8) (by omega_using [hw1]) (WordInv s B w N g r (w + (el + 7) / 8))
    (fun k _ hk u hu => word_ok M hc hp hGlt hG hk hu) (fun u hu => ?_) h0
  refine ⟨hu.frm, hu.keep, hu.ylt, ?_⟩
  have := hu.y
  rwa [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this

/-- The windowed exponentiation computes exactly the same padded power. -/
theorem exp_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g : Nat}
    (hc : Cst s B Z w minv N el r t) (hGlt : wv s.mem B (slot w aG) w < N)
    (hG : wv s.mem B (slot w aG) w % N = g * 2 ^ (64 * w) % N) :
    WP isa (windowExp M.mm) s fun u =>
      Frm B (rg w [aAcc, aTmp, aXm, aY, aE, aD] [sC1, sC2, sC3]) s.mem u.mem ∧
      Keep mmRegs s u ∧ wv u.mem B (slot w aY) w < N ∧
      wv u.mem B (slot w aY) w % N = g ^ r * 2 ^ (64 * w) % N := by
  unfold windowExp
  refine WP.seq (WP.mono (powers_ok M hc hGlt hG) fun u₁ ⟨hc₁, f₁, k₁, hp₁, hy₁⟩ => ?_)
  refine WP.mono (loop_ok M hc₁ hp₁ hp₁.g1lt hp₁.g1 hy₁) fun u ⟨f₂, k₂, hlt, hy⟩ =>
    ⟨(f₁.rg_trans f₂).rg_mono (by decide) (by decide), (k₁.trans k₂).mono (by decide), hlt, hy⟩

end RecoveryWindow
end VG.Proof.Rsa.X86_64
