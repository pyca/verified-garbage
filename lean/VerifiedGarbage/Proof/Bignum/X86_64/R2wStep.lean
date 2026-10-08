import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2

/-!
# `R² mod m` by word steps on x86-64: a step

`step`: `x := x 2^64 mod m` for `x < m` in `aR2` and `m` in `aN`, whose top
word is at least `2^63`, with the accumulator as `t` (`step_ok`).
-/

namespace VG.Proof.Bignum.X86_64.R2w

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

/-- `n + 1` words: the low `n` and the top one. -/
theorem wv_succ (m : Mem) (B : Addr) (e n : Nat) :
    wv m B e (n + 1) = wv m B e n + 2 ^ (64 * n) * (word m B (e + 8 * n)).toNat := rfl

/-- The top word of `x < m` is at most `m`'s. -/
theorem top_le {m : Mem} {B : Addr} {ex em w : Nat} (hw : 1 ≤ w)
    (h : wv m B ex w < wv m B em w) :
    (word m B (ex + 8 * (w - 1))).toNat ≤ (word m B (em + 8 * (w - 1))).toNat := by
  rw [show w = (w - 1) + 1 by omega, wv_succ, wv_succ] at h
  have h1 := wv_lt m B ex (w - 1)
  have h2 := wv_lt m B em (w - 1)
  rcases Nat.lt_or_ge (word m B (em + 8 * (w - 1))).toNat (word m B (ex + 8 * (w - 1))).toNat with hl | hl
  · exfalso
    have := Nat.mul_le_mul_left (2 ^ (64 * (w - 1))) (show (word m B (em + 8 * (w - 1))).toNat + 1 ≤
      (word m B (ex + 8 * (w - 1))).toNat by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · exact hl

/-- The sign of `t` (`w + 1` words) in two's complement is its top word's
top bit. -/
theorem top_half (m : Mem) (B : Addr) (e w : Nat) :
    2 ^ (64 * (w + 1)) / 2 ≤ wv m B e (w + 1) ↔ 2 ^ 63 ≤ (word m B (e + 8 * w)).toNat := by
  rw [wv_succ]
  have h1 := wv_lt m B e w
  have hW : 2 ^ (64 * (w + 1)) / 2 = 2 ^ (64 * w) * 2 ^ 63 := by
    rw [show 64 * (w + 1) = 64 * w + 63 + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide),
      Nat.pow_add]
  rw [hW]
  generalize 2 ^ (64 * w) = P at *
  generalize (word m B (e + 8 * w)).toNat = T
  constructor
  · intro h
    by_contra hc
    have := Nat.mul_le_mul_left P (show T + 1 ≤ 2 ^ 63 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · intro h
    exact Nat.le_trans (Nat.mul_le_mul_left P h) (Nat.le_add_left _ _)

/-- `step`'s loads: the bases of `x`, `m` and the accumulator, and `w`. -/
theorem stepBases_ok {L : Lay} {t : State} (hg : GoodL L t) :
    WP isa (.block R2Words.bases) t fun t' =>
      t'.gpr .rbx = off L.B (slot L.w aR2) ∧ t'.gpr .r10 = off L.B (slot L.w aN) ∧
      t'.gpr .r8 = off L.B (slot L.w aAcc) ∧ t'.gpr .r12 = BitVec.ofNat 64 L.w ∧ t'.mem = t.mem ∧
      Keep [.rbx, .r10, .r8, .r12] t t' := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot L.w 8 hi; have := hg.2; omega)
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .r12] (Q := fun t' =>
      t'.gpr .rbx = off L.B (slot L.w aR2) ∧ t'.gpr .r10 = off L.B (slot L.w aN) ∧
      t'.gpr .r8 = off L.B (slot L.w aAcc) ∧ t'.gpr .r12 = BitVec.ofNat 64 L.w ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold R2Words.bases
  xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide),
    hl (sArr aAcc) (by decide), hl sW (by decide), hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aN (by decide),
    hg.1.hdr.harr aAcc (by decide), hg.1.hdr.hw]

/-- `x := x 2^64 mod m`, for `x < m` in `aR2` and `m` in `aN`, `m`'s top word
at least `2^63`; it changes only the accumulator and `x`. -/
theorem step_ok {L : Lay} {t : State} (hg : GoodL L t) (hw : 2 ≤ L.w) (hw' : L.w < 2 ^ 30)
    (hd : 2 ^ 63 ≤ (word t.mem L.B (slot L.w aN + 8 * (L.w - 1))).toNat)
    (hx : wv t.mem L.B (slot L.w aR2) L.w < wv t.mem L.B (slot L.w aN) L.w) :
    WP isa step t fun t' => GoodL L t' ∧
      wv t'.mem L.B (slot L.w aR2) L.w = wv t.mem L.B (slot L.w aR2) L.w * 2 ^ 64 % wv t.mem L.B (slot L.w aN) L.w ∧
      Arrays L.B L.w [aAcc, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain ⟨B, Z, w, minv⟩ := L
  dsimp only at hw hw' hd hx ⊢
  have hs : Scr t B Z := hg.1.scr
  have hZ : slot w 8 ≤ Z := hg.2
  have hn : B.toNat + Z ≤ 2 ^ 64 := hs.nowrap
  have hsx := slot_le (w := w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := w) (show aN < 8 by decide)
  have hst := slot_le (w := w) (show aAcc < 8 by decide)
  have sXT := slot_sep (w := w) (show aR2 ≠ aAcc by decide)
  have sMT := slot_sep (w := w) (show aN ≠ aAcc by decide)
  rw [show step = .seq (.block R2Words.bases) (.seq quot (.seq mulSub (.seq addBack (.seq addBack copyBack))))
    from rfl]
  refine WP.seq (WP.mono (stepBases_ok (L := ⟨B, Z, w, minv⟩) hg) fun t₁ ⟨h1bx, h110, h18, h112, hm₁, k₁⟩ => ?_)
  dsimp only at h1bx h110 h18 h112
  have hs₁ := hs.congr k₁.2.2
  -- The values.
  generalize hX : wv t.mem B (slot w aR2) w = X at hx
  generalize hM : wv t.mem B (slot w aN) w = M at hx
  have hu := top_le (by omega) (hX ▸ hM ▸ hx)
  rw [← hm₁] at hu hd
  have e1 : slot w aR2 + 8 * w ≤ Z := by omega
  have e2 : slot w aN + 8 * w ≤ Z := by omega
  have e3 : 0 < (word t₁.mem B (slot w aN + 8 * (w - 1))).toNat := by omega
  have eT : slot w aAcc + 8 * (w + 1) ≤ Z := by omega
  have sX : slot w aAcc + 8 * (w + 1) ≤ slot w aR2 ∨ slot w aR2 + 8 * w ≤ slot w aAcc := by omega
  have sM : slot w aAcc + 8 * (w + 1) ≤ slot w aN ∨ slot w aN + 8 * w ≤ slot w aAcc := by omega
  have hw31 : w < 2 ^ 31 := by omega
  have hq := quot_ok hs₁ h1bx h110 h112 hw e1 e2 hu e3
  refine WP.seq (WP.mono hq fun t₂ ⟨h2cx, hm₂, k₂⟩ => ?_)
  generalize hqh : min (((word t₁.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ 64 +
    (word t₁.mem B (slot w aR2 + 8 * (w - 2))).toNat) / (word t₁.mem B (slot w aN + 8 * (w - 1))).toNat)
      (2 ^ 64 - 1) = qh at h2cx
  have hqh' : qh < 2 ^ 64 := by rw [← hqh]; exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hs₂ := hs₁.congr k₂.2.2
  have t₂bx : t₂.gpr .rbx = off B (slot w aR2) := (k₂.gpr (by decide)).trans h1bx
  have t₂10 : t₂.gpr .r10 = off B (slot w aN) := (k₂.gpr (by decide)).trans h110
  have t₂8 : t₂.gpr .r8 = off B (slot w aAcc) := (k₂.gpr (by decide)).trans h18
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (k₂.gpr (by decide)).trans h112
  have hms := mulSub_ok hs₂ t₂bx t₂10 t₂8 t₂12 hw hw31 e1 e2 eT sX sM
  refine WP.seq (WP.mono hms fun t₃ ⟨b, hv₃, ho₃, k₃⟩ => ?_)
  rw [h2cx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqh'] at hv₃
  have hs₃ := hs₂.congr k₃.2.2
  have t₃10 : t₃.gpr .r10 = off B (slot w aN) := (k₃.gpr (by decide)).trans t₂10
  have t₃8 : t₃.gpr .r8 = off B (slot w aAcc) := (k₃.gpr (by decide)).trans t₂8
  have t₃12 : t₃.gpr .r12 = BitVec.ofNat 64 w := (k₃.gpr (by decide)).trans t₂12
  have hab₃ := addBack_ok hs₃ t₃10 t₃8 t₃12 (by omega) hw31 e2 eT sM
  refine WP.seq (WP.mono hab₃ fun t₄ ⟨c1, hv₄, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have t₄10 : t₄.gpr .r10 = off B (slot w aN) := (k₄.gpr (by decide)).trans t₃10
  have t₄8 : t₄.gpr .r8 = off B (slot w aAcc) := (k₄.gpr (by decide)).trans t₃8
  have t₄12 : t₄.gpr .r12 = BitVec.ofNat 64 w := (k₄.gpr (by decide)).trans t₃12
  have hab₄ := addBack_ok hs₄ t₄10 t₄8 t₄12 (by omega) hw31 e2 eT sM
  refine WP.seq (WP.mono hab₄ fun t₅ ⟨c2, hv₅, ho₅, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  have t₅bx : t₅.gpr .rbx = off B (slot w aR2) :=
    (k₅.gpr (by decide)).trans ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans t₂bx))
  have t₅8 : t₅.gpr .r8 = off B (slot w aAcc) := (k₅.gpr (by decide)).trans t₄8
  have t₅12 : t₅.gpr .r12 = BitVec.ofNat 64 w := (k₅.gpr (by decide)).trans t₄12
  unfold copyBack
  refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t' => t'.gpr .rsi = off B (slot w aAcc) ∧ t'.mem = t₅.mem)
    (by xrun [t₅8]) rfl) fun t₆ ⟨⟨h6si, hm₆⟩, k₆⟩ => ?_)
  have hsepw : ∀ j < w, ∀ b < 8, ofs B (off B (slot w aAcc + 8 * j) + BitVec.ofNat 64 b) < slot w aR2 ∨
      slot w aR2 + 8 * w ≤ ofs B (off B (slot w aAcc + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
    rw [ofs_off B (by omega)]; omega
  have hs₆ := hs₅.congr k₆.2.2
  have hrd : ∀ j < w, InRegions (t₆.rd ++ t₆.wr) (off B (slot w aAcc + 8 * j)) 8 := fun j hj => hs₆.ld (by omega)
  have hwr : ∀ j < w, InRegions t₆.wr (off B (slot w aR2 + 8 * j)) 8 := fun j hj => hs₆.st (by omega)
  have hcw := copyWords_ok (S := B) (D := B) h6si ((k₆.gpr (by decide)).trans t₅bx)
    ((k₆.gpr (by decide)).trans t₅12) (by omega) hw31 (by omega) hrd hwr hsepw
  refine WP.mono hcw fun t' ⟨hc, _, ho', k'⟩ => ?_
  -- Memory: `m` and `x` as on entry until the copy; the accumulator's changes.
  have em3 : ∀ {d n}, d + 8 * n ≤ slot w aAcc ∨ slot w aAcc + 8 * (w + 2) ≤ d → d + 8 * n ≤ Z →
      wv t₃.mem B d n = wv t.mem B d n := fun h h' => by
    rw [ho₃.wv (by omega) (by omega), hm₂, hm₁]
  have em5 : ∀ {d n}, d + 8 * n ≤ slot w aAcc ∨ slot w aAcc + 8 * (w + 2) ≤ d → d + 8 * n ≤ Z →
      wv t₅.mem B d n = wv t.mem B d n := fun h h' => by
    rw [ho₅.wv (by omega) (by omega), ho₄.wv (by omega) (by omega), em3 h h']
  have wo3 : ∀ {d}, d + 8 ≤ slot w aAcc ∨ slot w aAcc + 8 * (w + 2) ≤ d → d + 8 ≤ Z →
      word t₃.mem B d = word t.mem B d := fun h h' => by
    rw [ho₃.word (by omega) (by omega), hm₂, hm₁]
  have wo4 : ∀ {d}, d + 8 ≤ slot w aAcc ∨ slot w aAcc + 8 * (w + 2) ≤ d → d + 8 ≤ Z →
      word t₄.mem B d = word t.mem B d := fun h h' => by
    rw [ho₄.word (by omega) (by omega), wo3 h h']
  rw [em3 (n := w) (d := slot w aN) (by omega) (by omega), hM] at hv₄
  rw [ho₄.wv (d := slot w aN) (k := w) (by omega) (by omega), em3 (n := w) (d := slot w aN) (by omega) (by omega),
    hM] at hv₅
  rw [hm₂, hm₁, hX, hM] at hv₃
  simp only [← top_half] at hv₄ hv₅
  -- The step's value.
  have hX' : X = (word t.mem B (slot w aR2 + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      (word t.mem B (slot w aR2 + 8 * (w - 2))).toNat * 2 ^ (64 * (w - 2)) + wv t.mem B (slot w aR2) (w - 2) := by
    rw [← hX, show w = (w - 2) + 1 + 1 by omega, wv_succ, wv_succ, show w - 2 + 1 + 1 - 1 = w - 2 + 1 by omega,
      show w - 2 + 1 + 1 - 2 = w - 2 by omega]
    grind
  have hM' : M = (word t.mem B (slot w aN + 8 * (w - 1))).toNat * 2 ^ (64 * (w - 1)) +
      wv t.mem B (slot w aN) (w - 1) := by
    rw [← hM, show w = (w - 1) + 1 by omega, wv_succ, show w - 1 + 1 - 1 = w - 1 by omega]; grind
  rw [hm₁] at hqh
  have hT3 := wordStep_val hw hX' (wv_lt _ _ _ _) hM' (wv_lt _ _ _ _) (by rw [← hm₁]; exact hd)
    (BitVec.isLt _) hx (wv_lt _ _ _ _) (Bool.toNat_lt b) (by rw [hqh]; exact hv₃) (wv_lt _ _ _ _)
    (Bool.toNat_lt c1) hv₄ (wv_lt _ _ _ _) (Bool.toNat_lt c2) hv₅
  have hlow : wv t₅.mem B (slot w aAcc) w = wv t₅.mem B (slot w aAcc) (w + 1) := by
    have hlt : wv t₅.mem B (slot w aAcc) (w + 1) < 2 ^ (64 * w) := by
      rw [hT3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) (hM ▸ wv_lt _ _ _ _)
    rw [wv_succ] at hlt ⊢
    have : (word t₅.mem B (slot w aAcc + 8 * w)).toNat = 0 := by
      by_contra h
      have := Nat.mul_le_mul_left (2 ^ (64 * w)) (show 1 ≤ (word t₅.mem B (slot w aAcc + 8 * w)).toNat by omega)
      omega
    rw [this, Nat.mul_zero, Nat.add_zero]
  have ha : Arrays B w [aAcc, aR2] t.mem t'.mem := by
    have e1 : slot w aAcc + 8 * (w + 1) ≤ slot w aAcc + 8 * (w + 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.le_succ _)) _
    have e2 : slot w aR2 + 8 * w ≤ slot w aR2 + 8 * (w + 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 8 (Nat.le_add_right _ _)) _
    have a3 : Arrays B w [aAcc, aR2] t₂.mem t₃.mem :=
      Arrays.of_outside (j := aAcc) (by simp) ho₃ (Nat.le_refl _) e1
    have a4 : Arrays B w [aAcc, aR2] t₃.mem t₄.mem :=
      Arrays.of_outside (j := aAcc) (by simp) ho₄ (Nat.le_refl _) e1
    have a5 : Arrays B w [aAcc, aR2] t₄.mem t₅.mem :=
      Arrays.of_outside (j := aAcc) (by simp) ho₅ (Nat.le_refl _) e1
    have a' : Arrays B w [aAcc, aR2] t₆.mem t'.mem :=
      Arrays.of_outside (j := aR2) (by simp) ho' (Nat.le_refl _) e2
    rw [hm₆] at a'
    rw [show t.mem = t₂.mem by rw [hm₂, hm₁]]
    exact ((a3.trans a4).trans a5).trans a'
  refine ⟨⟨⟨hs₅.congr (k'.2.2.trans k₆.2.2), ?_, ha.hdr hg.1.hdr⟩, hZ⟩, ?_, ha, ?_⟩
  · rw [k'.gpr (by decide), k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide),
      k₂.gpr (by decide), k₁.gpr (by decide)]; exact hg.1.rdi
  · rw [hc, hm₆, hlow, hT3]
  · exact (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans (k₆.trans k')).mono (by decide)

end VG.Proof.Bignum.X86_64.R2w
