module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtStep
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Pieces
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the corrections' composition, apart from the pieces' symbolic execution

/-!
# `vg_rsa_recover_primes_det` on x86-64: a digit's subtraction and corrections

From the estimate `q̂` (at most two above the digit `q`): `R - q̂ D`, the
corrections' addend, three corrections and `D`'s update leave the window the
remainder `R - (Y + q) q` and `D`'s window `Y + 2 q` (`corr_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem wv_one' (m : Mem) (B : Addr) (d : Nat) : wv m B d 1 = (word m B d).toNat := by
  simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]

/-- A number with its low word replaced. -/
theorem wv_w0 (m : Mem) (B : Addr) (d n : Nat) (v : BitVec 64) (hd : d + 8 * (n + 1) ≤ 2 ^ 64) :
    wv (m.writeW (off B d) v) B d (n + 1) = v.toNat + 2 ^ 64 * wv m B (d + 8) n := by
  rw [show n + 1 = 1 + n by omega, wv_add, show 64 * 1 = 64 from rfl, show d + 8 * 1 = d + 8 from rfl]
  have h1 : wv (m.writeW (off B d) v) B (d + 8) n = wv m B (d + 8) n :=
    (writeW_outside m B v (d := d) (by omega)).wv (by omega) (by omega)
  rw [h1, wv_one', word_writeW_self]

/-- A number with its low two words replaced. -/
theorem wv_w01 (m : Mem) (B : Addr) (d n : Nat) (lo hi : BitVec 64) (hd : d + 8 * (n + 2) ≤ 2 ^ 64) :
    wv ((m.writeW (off B d) lo).writeW (off B (d + 8)) hi) B d (n + 2) =
      lo.toNat + 2 ^ 64 * hi.toNat + 2 ^ 64 * 2 ^ 64 * wv m B (d + 16) n := by
  rw [show n + 2 = 1 + (1 + n) by omega, wv_add, wv_add, show 64 * 1 = 64 from rfl, show d + 8 * 1 = d + 8 from rfl,
    show d + 8 + 8 = d + 16 by omega]
  have o2 := writeW_outside (m.writeW (off B d) lo) B hi (d := d + 8) (by omega)
  have o1 := writeW_outside m B lo (d := d) (by omega)
  have h0 : wv ((m.writeW (off B d) lo).writeW (off B (d + 8)) hi) B d 1 = lo.toNat := by
    rw [wv_one', o2.word (by omega) (by omega), word_writeW_self]
  have h1 : wv ((m.writeW (off B d) lo).writeW (off B (d + 8)) hi) B (d + 8) 1 = hi.toNat := by
    rw [wv_one', word_writeW_self]
  have h2 : wv ((m.writeW (off B d) lo).writeW (off B (d + 8)) hi) B (d + 16) n = wv m B (d + 16) n := by
    rw [o2.wv (by omega) (by omega), o1.wv (by omega) (by omega)]
  rw [h0, h1, h2]
  grind

/-- A number's low two words and the rest. -/
theorem wv_two (m : Mem) (B : Addr) (d n : Nat) :
    wv m B d (n + 2) = (word m B d).toNat + 2 ^ 64 * (word m B (d + 8)).toNat + 2 ^ 64 * 2 ^ 64 * wv m B (d + 16) n := by
  rw [show n + 2 = 1 + (1 + n) by omega, wv_add, wv_add, show 64 * 1 = 64 from rfl, show d + 8 * 1 = d + 8 from rfl,
    show d + 8 + 8 = d + 16 by omega, wv_one', wv_one']
  grind

/-- The top word of a number of `L` words. -/
theorem top_word (m : Mem) (B : Addr) (d L : Nat) (hL : 1 ≤ L) :
    (word m B (d + 8 * (L - 1))).toNat = wv m B d L / 2 ^ (64 * (L - 1)) := by
  rw [word_of_wv m B d L (q := L - 1) (by omega), Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 64 + 64 * (L - 1) = 64 * L by omega]
  exact wv_lt _ _ _ _

/-- The top bit of the top word of `w < M = 2^(64 L)`: `M ≤ 2 w`. -/
theorem top_bit_iff {w L : Nat} (hL : 1 ≤ L) :
    2 ^ 63 ≤ w / 2 ^ (64 * (L - 1)) ↔ 2 ^ (64 * L) ≤ 2 * w := by
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), show 64 * L = 1 + 63 + 64 * (L - 1) by omega, Nat.pow_add,
    Nat.pow_add, Nat.mul_assoc]
  omega

/-- The corrections' state at count `c`, from `s₀`: the window `w`, `D`'s low
two words `e` (and its others those of `Y`'s), the candidate `t`. -/
structure FS (s₀ : State) (B : Addr) (Z W h c Y R q y1 Yhi : Nat) (t : State) (w e tt : Nat) : Prop where
  ws : Ws t B Z W
  ct : word t.mem B (8 * sCt) = BitVec.ofNat 64 c
  win : wv t.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = w
  dlo : (word t.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat * 2 ^ 64 +
    (word t.mem B (slot W sqD + 8 * (c - 1))).toNat = e
  dhi : wv t.mem B (slot W sqD + 8 * (c - 1) + 16) (h - (c - 1)) = Yhi
  inv : FixInv (2 ^ 64) (2 ^ (64 * (h - (c - 1) + 2))) Y R q y1 w e tt
  frm : FrmP B (fun y => (slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
    (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

/-- A correction. -/
theorem fixStep_ok {s₀ t : State} {B : Addr} {Z W h c Y R q y1 Yhi w e tt : Nat} (hwh : W = 2 * h + 4)
    (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) (hY : Y = 2 ^ 64 * 2 ^ 64 * Yhi + y1 * 2 ^ 64) (hy1 : y1 + 2 ≤ 2 ^ 64)
    (hqβ : q < 2 ^ 64) (lo : (Y + q) * q ≤ R) (hi : R < (Y + (q + 1)) * (q + 1))
    (hR2 : 2 * R < 2 ^ (64 * (h - (c - 1) + 2))) (hB : 2 * ((Y + (q + 2)) * (q + 2)) < 2 ^ (64 * (h - (c - 1) + 2)))
    (hF : FS s₀ B Z W h c Y R q y1 Yhi t w e tt) :
    WP isa fixX t fun t' => ∃ w' e', FS s₀ B Z W h c Y R q y1 Yhi t' w' e' (if q < tt then tt - 1 else tt) := by
  have hn := hF.ws.scr.nowrap
  have hw2 := hF.ws.w2
  have hZ := hF.ws.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  refine WP.mono (fixX_ok hF.ws hwh hF.ct hc1 hch) fun t' ⟨m, c', lo', hi', hv, ho, hm, hval, k⟩ => ?_
  have hL : 1 ≤ h - (c - 1) + 2 := by omega
  -- The sign, as `M ≤ 2 w`.
  have hsign : (2 ^ 63 ≤ (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1))).toNat) ↔
      2 ^ (64 * (h - (c - 1) + 2)) ≤ 2 * w := by
    rw [top_word _ _ _ _ hL, hF.win]; exact top_bit_iff hL
  have hneg := fix_neg lo hi hR2 hB hF.inv
  -- `D`'s window: `Y_top + e`.
  have hD : wv t.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = 2 ^ 64 * 2 ^ 64 * Yhi + e := by
    rw [wv_two, hF.dhi, ← hF.dlo]; grind
  -- The window and `D`'s words after.
  have o1 := writeW_outside m B lo' (d := slot W sqD + 8 * (c - 1)) (by omega)
  have o2 := writeW_outside (m.writeW (off B (slot W sqD + 8 * (c - 1))) lo') B hi'
    (d := slot W sqD + 8 * (c - 1) + 8) (by omega)
  have win' : wv t'.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) =
      wv m B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) := by
    rw [hm, o2.wv (by omega) (by omega), o1.wv (by omega) (by omega)]
  have dlo' : (word t'.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat * 2 ^ 64 +
      (word t'.mem B (slot W sqD + 8 * (c - 1))).toNat = hi'.toNat * 2 ^ 64 + lo'.toNat := by
    rw [hm, word_writeW_self, o2.word (by omega) (by omega), word_writeW_self]
  have dhi' : wv t'.mem B (slot W sqD + 8 * (c - 1) + 16) (h - (c - 1)) = Yhi := by
    rw [hm, o2.wv (by omega) (by omega), o1.wv (by omega) (by omega), ho.wv (by omega) (by omega), hF.dhi]
  have FP : FrmP B (fun y => (slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
      (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) t.mem t'.mem := by
    intro x hx
    rw [hm, o2 x (by omega), o1 x (by omega), ho x (by omega)]
  refine ⟨wv m B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2), hi'.toNat * 2 ^ 64 + lo'.toNat,
    hF.ws.congrP FP (fun y hy => by unfold DOk; omega) k (by decide), ?_, win', dlo', dhi', ?_,
    hF.frm.trans (FP.mono fun y hy => hy), hF.keep.trans k |>.mono (by decide)⟩
  · rw [FP.word_eq (fun y h1 h2 hy => by simp only [sCt, sFn] at h1 h2; omega) (by simp only [sCt, sFn]; omega), hF.ct]
  · have hif : (if q < tt then tt - 1 else tt) = (if 2 ^ (64 * (h - (c - 1) + 2)) ≤ 2 * w then tt - 1 else tt) := by
      by_cases hq : q < tt
      · simp only [hq, hneg.mpr hq, ↓reduceIte]
      · have hn' : ¬ 2 ^ (64 * (h - (c - 1) + 2)) ≤ 2 * w := fun h => hq (hneg.mp h)
        simp only [hq, hn', ↓reduceIte]
    rw [hif]
    refine fix_inv (Ytop := 2 ^ 64 * 2 ^ 64 * Yhi) (c' := c') (by rw [hY]) hy1 hqβ lo hi hR2 hB hF.inv ?_ (wv_lt _ _ _ _) ?_
    · rw [hv, hF.win, hD]
      by_cases hs : 2 ^ (64 * (h - (c - 1) + 2)) ≤ 2 * w
      · simp only [hsign.mpr hs, hs, ↓reduceIte]
      · have hn' : ¬ 2 ^ 63 ≤ (word t.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1))).toNat :=
          fun h => hs (hsign.mp h)
        simp only [hn', hs, ↓reduceIte]
    · rw [hval, hF.dlo, ← pow128, show decide (2 ^ 63 ≤ (word t.mem B (slot W sqZ + 16 * (c - 1) +
        8 * (h - (c - 1) + 2 - 1))).toNat) = decide (2 ^ (64 * (h - (c - 1) + 2)) ≤ 2 * w) from
          decide_eq_decide.mpr hsign]


/-- The subtraction and the corrections: from the window `R`, `D`'s window
`Y` (its low word zero) and the estimate `q̂` (`sU`) of the digit `q`, the
window `R - (Y + q) q` and `D`'s `Y + 2 q`. -/
theorem corr_ok {s : State} {B : Addr} {Z W h c : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) {R Y q qh : Nat}
    (hR : wv s.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = R)
    (hY : wv s.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = Y)
    (hY0 : word s.mem B (slot W sqD + 8 * (c - 1)) = 0)
    (hy1 : (word s.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat + 2 ≤ 2 ^ 64)
    (hqh : word s.mem B (8 * sU) = BitVec.ofNat 64 qh) (hqhβ : qh < 2 ^ 64) (hqβ : q < 2 ^ 64)
    (lo : (Y + q) * q ≤ R) (hi : R < (Y + (q + 1)) * (q + 1)) (hq1 : q ≤ qh) (hq2 : qh ≤ q + 2)
    (hR2 : 2 * R < 2 ^ (64 * (h - (c - 1) + 2))) (hB : 2 * ((Y + (q + 2)) * (q + 2)) < 2 ^ (64 * (h - (c - 1) + 2))) :
    WP isa (.seq mulSubX (.seq (.block toE) (.seq fixX (.seq fixX (.seq fixX (.block updX)))))) s fun t =>
      wv t.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) = R - (Y + q) * q ∧
      wv t.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) = Y + 2 * q ∧
      FrmP B (fun y => (slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
        (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) s.mem t.mem ∧
      Keep mmRegs s t ∧ Ws t B Z W := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  generalize hy1d : (word s.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat = y1 at hy1
  generalize hYhi : wv s.mem B (slot W sqD + 8 * (c - 1) + 16) (h - (c - 1)) = Yhi
  have hYv : Y = 2 ^ 64 * 2 ^ 64 * Yhi + y1 * 2 ^ 64 := by
    rw [← hY, show h - (c - 1) + 2 = (h - (c - 1)) + 2 from rfl, wv_two, hY0, hy1d, hYhi]
    simp only [show (0 : BitVec 64).toNat = 0 from rfl]; grind
  -- `R - q̂ D`.
  refine WP.seq (WP.mono (mulSubX_ok hw hwh hc hc1 hch hqh hqhβ) fun t₁ ⟨k₀, hv₁, ho₁, k₁⟩ => ?_)
  have hD1 : wv (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) (BitVec.ofNat 64 qh)) B (slot W sqD + 8 * (c - 1))
      (h - (c - 1) + 2) = qh + Y := by
    rw [show h - (c - 1) + 2 = (h - (c - 1) + 1) + 1 from rfl, wv_w0 _ _ _ _ _ (by omega), ← hY,
      show h - (c - 1) + 1 + 1 = 0 + 1 + (h - (c - 1) + 1) by omega, wv_add, wv_add]
    simp only [wv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqhβ]
    grind
  rw [hD1, hR] at hv₁
  have FP₁ : FrmP B (fun y => (slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
      (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) s.mem t₁.mem := by
    intro x hx
    rw [ho₁ x (by omega), writeW_outside s.mem B _ (d := slot W sqD + 8 * (c - 1)) (by omega) x (by omega)]
  have hw₁ := hw.congrP FP₁ (fun y hy => by unfold DOk; omega) k₁ (by decide)
  have ct₁ : word t₁.mem B (8 * sCt) = BitVec.ofNat 64 c := by
    rw [FP₁.word_eq (fun y h1 h2 hy => by simp only [sCt, sFn] at h1 h2; omega) (by simp only [sCt, sFn]; omega), hc]
  have lo₁ : word t₁.mem B (slot W sqD + 8 * (c - 1)) = BitVec.ofNat 64 qh := by
    rw [ho₁.word (by omega) (by omega), word_writeW_self]
  have hi₁ : (word t₁.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat = y1 := by
    rw [ho₁.word (by omega) (by omega), (writeW_outside s.mem B _ (d := slot W sqD + 8 * (c - 1)) (by omega)).word
      (by omega) (by omega), hy1d]
  have Yhi₁ : wv t₁.mem B (slot W sqD + 8 * (c - 1) + 16) (h - (c - 1)) = Yhi := by
    rw [ho₁.wv (by omega) (by omega), (writeW_outside s.mem B _ (d := slot W sqD + 8 * (c - 1)) (by omega)).wv
      (by omega) (by omega), hYhi]
  -- The corrections' addend.
  refine WP.seq (WP.mono (toE_ok hw₁ hwh ct₁ hc1 hch) fun t₂ ⟨lo₂, hi₂, hm₂, hval₂, k₂⟩ => ?_)
  rw [lo₁, hi₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqhβ] at hval₂
  have o1 := writeW_outside t₁.mem B lo₂ (d := slot W sqD + 8 * (c - 1)) (by omega)
  have o2 := writeW_outside (t₁.mem.writeW (off B (slot W sqD + 8 * (c - 1))) lo₂) B hi₂
    (d := slot W sqD + 8 * (c - 1) + 8) (by omega)
  have FP₂ : FrmP B (fun y => (slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
      (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) t₁.mem t₂.mem := by
    intro x hx
    rw [hm₂, o2 x (by omega), o1 x (by omega)]
  have F₂ : FS s B Z W h c Y R q y1 Yhi t₂ (wv t₁.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2))
      (hi₂.toNat * 2 ^ 64 + lo₂.toNat) qh := by
    refine ⟨hw₁.congrP FP₂ (fun y hy => by unfold DOk; omega) k₂ (by decide), ?_, ?_, ?_, ?_, ?_,
      FP₁.trans FP₂, (k₁.trans k₂).mono (by decide)⟩
    · rw [FP₂.word_eq (fun y h1 h2 hy => by simp only [sCt, sFn] at h1 h2; omega) (by simp only [sCt, sFn]; omega), ct₁]
    · rw [hm₂, o2.wv (by omega) (by omega), o1.wv (by omega) (by omega)]
    · rw [hm₂, word_writeW_self, o2.word (by omega) (by omega), word_writeW_self]
    · rw [hm₂, o2.wv (by omega) (by omega), o1.wv (by omega) (by omega), Yhi₁]
    · refine ⟨hq1, hq2, hqhβ, wv_lt _ _ _ _, ⟨k₀, ?_⟩, ?_⟩
      · have : (wv t₁.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) : Int) + (qh * (qh + Y) : Nat) =
            R + (2 ^ (64 * (h - (c - 1) + 2)) * k₀ : Nat) := by exact_mod_cast hv₁
        rw [show (Y + qh) * qh = qh * (qh + Y) by grind]
        push_cast at this ⊢
        omega
      · rw [hval₂, ← pow128]
  -- Three corrections.
  refine WP.seq (WP.mono (fixStep_ok hwh hc1 hch hYv hy1 hqβ lo hi hR2 hB F₂) fun t₃ ⟨w₃, e₃, F₃⟩ => ?_)
  refine WP.seq (WP.mono (fixStep_ok hwh hc1 hch hYv hy1 hqβ lo hi hR2 hB F₃) fun t₄ ⟨w₄, e₄, F₄⟩ => ?_)
  refine WP.seq (WP.mono (fixStep_ok hwh hc1 hch hYv hy1 hqβ lo hi hR2 hB F₄) fun t₅ ⟨w₅, e₅, F₅⟩ => ?_)
  have hq : (if q < (if q < (if q < qh then qh - 1 else qh) then (if q < qh then qh - 1 else qh) - 1 else
      (if q < qh then qh - 1 else qh)) then (if q < (if q < qh then qh - 1 else qh) then
        (if q < qh then qh - 1 else qh) - 1 else (if q < qh then qh - 1 else qh)) - 1 else
      (if q < (if q < qh then qh - 1 else qh) then (if q < qh then qh - 1 else qh) - 1 else
        (if q < qh then qh - 1 else qh))) = q := by
    rcases (show qh = q ∨ qh = q + 1 ∨ qh = q + 2 by omega) with rfl | rfl | rfl <;> simp
  rw [hq] at F₅
  obtain ⟨hw5, he5⟩ := fix_final (by omega) lo hR2 F₅.inv
  -- `D`'s update.
  refine WP.mono (updX_ok F₅.ws hwh F₅.ct hc1 hch) fun t ⟨lo', hi'', hm, hval, k⟩ => ?_
  rw [F₅.dlo] at hval
  have o1 := writeW_outside t₅.mem B lo' (d := slot W sqD + 8 * (c - 1)) (by omega)
  have o2 := writeW_outside (t₅.mem.writeW (off B (slot W sqD + 8 * (c - 1))) lo') B hi''
    (d := slot W sqD + 8 * (c - 1) + 8) (by omega)
  have FP : FrmP B (fun y => (slot W sqZ + 16 * (c - 1) ≤ y ∧ y < slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2)) ∨
      (slot W sqD + 8 * (c - 1) ≤ y ∧ y < slot W sqD + 8 * (c - 1) + 16)) t₅.mem t.mem := by
    intro x hx
    rw [hm, o2 x (by omega), o1 x (by omega)]
  refine ⟨?_, ?_, F₅.frm.trans FP, F₅.keep.trans k |>.mono (by decide),
    F₅.ws.congrP FP (fun y hy => by unfold DOk; omega) k (by decide)⟩
  · rw [hm, o2.wv (by omega) (by omega), o1.wv (by omega) (by omega), F₅.win, hw5]
  · rw [hm, show h - (c - 1) + 2 = (h - (c - 1)) + 2 from rfl, wv_w01 _ _ _ _ _ _ (by omega), F₅.dhi, hYv]
    rw [pow128] at hval
    have : hi''.toNat * 2 ^ 64 + lo'.toNat = y1 * 2 ^ 64 + 2 * q := by rw [hval, he5]
    omega


end VG.Proof.Rsa.X86_64.Rd
