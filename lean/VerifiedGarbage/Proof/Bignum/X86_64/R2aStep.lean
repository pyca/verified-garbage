import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep

/-!
# `R² mod m` by word steps with ADX: a step

`R2Adx.fix` adds `m` back to `t` if its top word's sign bit is set, by a
branch, as `R2Words.addBack` does by a mask (`fix_ok`, the same statement);
`R2Adx.step` is `x := x 2^64 mod m` (`step_ok`, as `R2w.step_ok`), with the
accumulator holding `mc = R - m`.
-/

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem top_cf (x : BitVec 64) : decide (2 ^ 64 ≤ x.toNat + x.toNat) = decide (2 ^ 63 ≤ x.toNat) :=
  decide_eq_decide.mpr (by omega)

/-- `t := t + m` if `t` is negative (its top word's top bit set). -/
theorem fix_ok {s : State} {B : Addr} {Z w em et : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B em) (hbx : s.gpr .rbx = off B et) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hM : em + 8 * w ≤ Z) (hT : et + 8 * (w + 1) ≤ Z)
    (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et) :
    WP isa fix s fun t => ∃ c : Bool,
      wv t.mem B et (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat = wv s.mem B et (w + 1) +
        (if 2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat then wv s.mem B em w else 0) ∧
      Outside B et (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .r8, .r11, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have hea : s.ea (ix .rbx .r12) = off B (et + 8 * w) := ea_ix0 s hbx h12
  unfold fix
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat)) ∧
      t.mem = s.mem) (by xrun [hea, hs.ld (show et + 8 * w + 8 ≤ Z by omega), top_cf]) rfl)
    fun t₁ ⟨⟨hc₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine WP.ite (decide (2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat)) (by simp only [eval, hc₁]) (fun hb => ?_)
    (fun hb => ?_)
  · refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off B et ∧ t.mem = t₁.mem) (by
      xrun [(k₁.gpr (by decide)).trans hbx]) rfl) fun t₂ ⟨⟨h8, hm₂⟩, k₂⟩ => ?_)
    have k₁₂ := k₁.trans k₂
    refine WP.mono (R2w.addBack_ok (hs₁.congr k₂.2.2) ((k₁₂.gpr (by decide)).trans h10) h8
      ((k₁₂.gpr (by decide)).trans h12) hw hw' hM hT sM) fun t ⟨c, hv, ho, k⟩ => ⟨c, ?_, ?_, ?_⟩
    · rw [hv, hm₂, hm₁]
    · rw [← hm₁, ← hm₂]; exact ho
    · exact (k₁₂.trans k).mono (by decide)
  · refine WP.block_nil ⟨false, ?_, by rw [hm₁]; exact Outside.refl _ _ _ _, k₁.mono (by decide)⟩
    have : ¬ 2 ^ 63 ≤ (word s.mem B (et + 8 * w)).toNat := by simpa using hb
    simp only [this, ↓reduceIte, hm₁, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

theorem mod_cancel {r D E W : Nat} (hr : r < W) (hD : D < W) (h : (r + E) % W = (D + E) % W) : r = D := by
  have h1 := Nat.div_add_mod (r + E) W
  have h2 := Nat.div_add_mod (D + E) W
  rcases Nat.lt_trichotomy ((r + E) / W) ((D + E) / W) with hl | he | hg
  · have := Nat.mul_le_mul_left W (show (r + E) / W + 1 ≤ (D + E) / W by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  · rw [he] at h1; omega
  · have := Nat.mul_le_mul_left W (show (D + E) / W + 1 ≤ (r + E) / W by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega

/-- `t = x 2^64 - q̂ m` from the computed `t + q̂ R ≡ x 2^64 + q̂ (R - m)`: as
`R2w.mulSub_ok` states it, with a borrow `b`. -/
theorem sub_val {T q M X C R W : Nat} (hW : W = R * 2 ^ 64) (hC : C + M = R) (hT : T < W) (hq : q < 2 ^ 64)
    (hX : X < M) (h : (T + q * R) % W = (X * 2 ^ 64 + q * C) % W) :
    ∃ b : Bool, T + q * M = X * 2 ^ 64 + W * b.toNat := by
  have hXW : X * 2 ^ 64 < W := by rw [hW]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by decide)
  have hqM : q * M < W := by
    rw [hW, Nat.mul_comm R]; exact Nat.mul_lt_mul_of_lt_of_le hq (by omega) (by omega)
  have e : (T + q * M) % W = X * 2 ^ 64 := by
    have hA := Nat.div_add_mod (T + q * M) W
    have h' : ((T + q * M) % W + q * C) % W = (X * 2 ^ 64 + q * C) % W := by
      rw [← h, ← hC, Nat.mul_add, Nat.add_mod ((T + q * M) % W), Nat.mod_mod, ← Nat.add_mod,
        show T + (q * C + q * M) = T + q * M + q * C by omega]
    exact mod_cancel (Nat.mod_lt _ (by omega)) hXW h'
  by_cases hb : T + q * M < W
  · exact ⟨false, by rw [Nat.mod_eq_of_lt hb] at e; simp [e]⟩
  · refine ⟨true, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at e
    simp only [Bool.toNat_true, Nat.mul_one]; omega

/-- `x := x 2^64 mod m`, for `x < m` in `aR2`, `m` in `aN` (`w` a multiple of 4
words, its top word `d` at least `2^63`), `v` the first word of the
temporary and `R - m` in the accumulator; it changes only `x`. -/
theorem step_ok {L : Lay} {t : State} (hg : GoodL L t) (hw : 4 ≤ L.w) (hw4 : L.w % 4 = 0) (hw' : L.w < 2 ^ 30)
    (hd : 2 ^ 63 ≤ (word t.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat)
    (hv : (word t.mem L.B (slot L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word t.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat - 2 ^ 64)
    (hx : wv t.mem L.B (slot L.w aR2) L.w < wv t.mem L.B (slot L.w aN) L.w)
    (hc : wv t.mem L.B (slot L.w aAcc) L.w + wv t.mem L.B (slot L.w aN) L.w = 2 ^ (64 * L.w)) :
    WP isa step t fun t' => GoodL L t' ∧
      wv t'.mem L.B (slot L.w aR2) L.w = wv t.mem L.B (slot L.w aR2) L.w * 2 ^ 64 % wv t.mem L.B (slot L.w aN) L.w ∧
      Arrays L.B L.w [aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain ⟨B, Z, w, minv⟩ := L
  dsimp only at hw hw4 hw' hd hv hx hc ⊢
  have hs : Scr t B Z := hg.1.scr
  have hZ : slot w 8 ≤ Z := hg.2
  have hn : B.toNat + Z ≤ 2 ^ 64 := hs.nowrap
  have hsx := slot_le (w := w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := w) (show aN < 8 by decide)
  have hst := slot_le (w := w) (show aAcc < 8 by decide)
  have sXT := slot_sep (w := w) (show aR2 ≠ aAcc by decide)
  have sXM := slot_sep (w := w) (show aR2 ≠ aN by decide)
  have hsv := slot_le (w := w) (show aTmp < 8 by decide)
  have hhd := hdr_lt_slot w 0 (show sArr aAcc < 32 by decide)
  have hs0 := slot_le (w := w) (show 0 < 8 by decide)
  rw [show step = .seq (.block R2Words.bases) (.seq (.block R2Words.quot) (.seq mulSub (.seq fix fix))) from rfl]
  refine WP.seq (WP.mono (R2w.stepBases_ok (L := ⟨B, Z, w, minv⟩) hg)
    fun t₁ ⟨h1bx, h110, _, h112, h1bp, hm₁, k₁⟩ => ?_)
  dsimp only at h1bx h110 h112 h1bp
  have hs₁ := hs.congr k₁.2.2
  generalize hX : wv t.mem B (slot w aR2) w = X at hx
  generalize hM : wv t.mem B (slot w aN) w = M at hx hc
  have hu := R2w.top_le (by omega) (hX ▸ hM ▸ hx)
  rw [← hm₁] at hu hd hv
  have e1 : slot w aR2 + 8 * w ≤ Z := by omega
  have e2 : slot w aN + 8 * w ≤ Z := by omega
  have e3 : slot w aTmp + 8 ≤ Z := by omega
  have hw31 : w < 2 ^ 31 := by omega
  have hq := R2w.quot_ok hs₁ h1bx h110 h112 h1bp (by omega) e1 e2 e3 hu hd hv
  refine WP.seq (WP.mono hq fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  generalize hqh : min (((word t₁.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 +
    (word t₁.mem B (slot w aR2 + 8 * (w - 2))).toNat) / (word t₁.mem B (slot w aN + 8 * (w - 1))).toNat)
      (2 ^ 64 - 1) = qh at h2cx
  have hqh' : qh < 2 ^ 64 := by rw [← hqh]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hs₂ := hs₁.congr k₂.2.2
  have k₁₂ := k₁.trans k₂
  have t₂bx : t₂.gpr .rbx = off B (slot w aR2) := (k₂.gpr (by decide)).trans h1bx
  have t₂10 : t₂.gpr .r10 = off B (slot w aN) := (k₂.gpr (by decide)).trans h110
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h112
  have t₂di : t₂.gpr .rdi = B := (k₁₂.gpr (by decide)).trans hg.1.rdi
  have hA : word t₂.mem B (8 * sArr aAcc) = off B (slot w aAcc) := by
    rw [hm₂, hm₁]; exact hg.1.hdr.harr aAcc (by decide)
  have hms := mulSub_ok (N := w / 4) hs₂ t₂di hA (by omega) t₂bx t₂12 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  refine WP.seq (WP.mono hms fun t₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  rw [h2cx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqh', hm₂, hm₁, hX] at hv₃
  rw [hm₂, hm₁] at ho₃
  have hs₃ := hs₂.congr k₃.2.2
  have k₁₃ := k₁₂.trans k₃
  have t₃10 : t₃.gpr .r10 = off B (slot w aN) := (k₃.gpr (by decide)).trans t₂10
  have t₃bx : t₃.gpr .rbx = off B (slot w aR2) := (k₃.gpr (by decide)).trans t₂bx
  have t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans t₂12
  have sM : slot w aR2 + 8 * (w + 1) ≤ slot w aN ∨ slot w aN + 8 * w ≤ slot w aR2 := by omega
  refine WP.seq (WP.mono (fix_ok hs₃ t₃10 t₃bx t₃12 (by omega) hw31 e2 (by omega) sM) fun t₄ ⟨c1, hv₄, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have t₄10 : t₄.gpr .r10 = off B (slot w aN) := (k₄.gpr (by decide)).trans t₃10
  have t₄bx : t₄.gpr .rbx = off B (slot w aR2) := (k₄.gpr (by decide)).trans t₃bx
  have t₄12 : t₄.gpr .r12 = BitVec.ofNat 64 w := (k₄.gpr (by decide)).trans t₃12
  refine WP.mono (fix_ok hs₄ t₄10 t₄bx t₄12 (by omega) hw31 e2 (by omega) sM) fun t' ⟨c2, hv₅, ho₅, k₅⟩ => ?_
  -- `m`, the accumulator and the top words are as on entry outside `x`.
  have em3 : ∀ {d n}, d + 8 * n ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ d → d + 8 * n ≤ Z →
      wv t₃.mem B d n = wv t.mem B d n := fun h h' => ho₃.wv (by omega) (by omega)
  have em4 : ∀ {d n}, d + 8 * n ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ d → d + 8 * n ≤ Z →
      wv t₄.mem B d n = wv t.mem B d n := fun h h' => by rw [ho₄.wv (by omega) (by omega), em3 h h']
  rw [em3 (n := w) (d := slot w aN) (by omega) (by omega), hM] at hv₄
  rw [em4 (n := w) (d := slot w aN) (by omega) (by omega), hM] at hv₅
  simp only [← R2w.top_half] at hv₄ hv₅
  -- `t`'s value with the borrow.
  have hC : wv t.mem B (slot w aAcc) w + M = 2 ^ (64 * w) := hc
  obtain ⟨b, hb⟩ := sub_val (T := wv t₃.mem B (slot w aR2) (w + 1)) (q := qh) (R := 2 ^ (64 * w))
    (W := 2 ^ (64 * (w + 1))) (by rw [show 64 * (w + 1) = 64 * w + 64 by omega, Nat.pow_add]) hC (wv_lt _ _ _ _)
    hqh' hx hv₃
  have hX' : X = (word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv t.mem B (slot w aR2) (w - 2) := by
    rw [← hX, show w = (w - 2) + 1 + 1 by omega, wv_succ, wv_succ, show w - 2 + 1 + 1 - 1 = w - 2 + 1 by omega,
      show w - 2 + 1 + 1 - 2 = w - 2 by omega]
    grind
  have hM' : M = (word t.mem B (slot w aN + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      wv t.mem B (slot w aN) (w - 1) := by
    rw [← hM, show w = (w - 1) + 1 by omega, wv_succ, show w - 1 + 1 - 1 = w - 1 by omega]; grind
  rw [hm₁] at hqh
  have hT3 := WordStep.wordStep_val (by omega) hX' (wv_lt _ _ _ _) hM' (wv_lt _ _ _ _) (by rw [← hm₁]; exact hd)
    (BitVec.isLt _) hx (wv_lt _ _ _ _) (Bool.toNat_lt b) (by rw [hqh]; exact hb) (wv_lt _ _ _ _)
    (Bool.toNat_lt c1) hv₄ (wv_lt _ _ _ _) (Bool.toNat_lt c2) hv₅
  have hlow : wv t'.mem B (slot w aR2) w = wv t'.mem B (slot w aR2) (w + 1) := by
    have hlt : wv t'.mem B (slot w aR2) (w + 1) < 2 ^ (64 * w) := by
      rw [hT3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) (hM ▸ wv_lt _ _ _ _)
    rw [wv_succ] at hlt ⊢
    have : (word t'.mem B (slot w aR2 + 8 * w)).toNat = 0 := by
      by_contra h
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤ (word t'.mem B (slot w aR2 + 8 * w)).toNat by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  have ha : Arrays B w [aR2] t.mem t'.mem := by
    have e4 : slot w aR2 + 8 * (w + 1) ≤ slot w aR2 + 8 * (w + 2) := by omega
    exact ((Arrays.of_outside (j := aR2) (by simp) ho₃ (Nat.le_refl _) e4).trans
      (Arrays.of_outside (j := aR2) (by simp) ho₄ (Nat.le_refl _) e4)).trans
      (Arrays.of_outside (j := aR2) (by simp) ho₅ (Nat.le_refl _) e4)
  have k' := (k₁₃.trans k₄).trans k₅
  refine ⟨⟨⟨hs₄.congr k₅.2.2, (k'.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, ?_, ha,
    k'.mono (by decide)⟩
  rw [hlow, hT3]

end VG.Proof.Bignum.X86_64.R2ax
