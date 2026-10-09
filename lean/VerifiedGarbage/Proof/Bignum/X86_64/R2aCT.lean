import VerifiedGarbage.Proof.Bignum.X86_64.R2aFast
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT

/-!
# `R² mod m` by word steps with ADX: constant time but for `m`

A step's addresses depend only on the working space and `w`, and its
branches, `fix`'s, on the sign of `t`, a function of `x` and `m`: in the
steps, `x` is `(R - m) 2^(64 j) mod m` after `j` of them, a function of `m`,
which is public (`SPub`, `step_ct`). The steps' count is `w` (`steps_ct`),
and `choice` branches on the top bit of `m` and on `w` (`choice_ct`).
-/

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep

/-! ## A step -/

/-- The public data of a step: the working space, `x` and `m`. -/
structure SPub where
  L : Lay
  X : Nat
  M : Nat

/-- `R` and `2^64 R`. -/
abbrev SPub.R (p : SPub) : Nat := 2 ^ (64 * p.L.w)
abbrev SPub.W (p : SPub) : Nat := 2 ^ (64 * (p.L.w + 1))

/-- `q̂`, from the top words of `x` and `m`. -/
def SPub.q (p : SPub) : Nat :=
  min ((p.X / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64 * 2 ^ 64 + p.X / 2 ^ (64 * (p.L.w - 2)) % 2 ^ 64) /
    (p.M / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64)) (2 ^ 64 - 1)

/-- `t = x 2^64 - q̂ m` modulo `2^64 R`. -/
def SPub.t1 (p : SPub) : Nat := (p.X * 2 ^ 64 + p.q * (p.R - p.M) + p.q * (p.W - p.R)) % p.W

/-- `t + m` if `t` is negative. -/
def fixV (W M T : Nat) : Nat := if W / 2 ≤ T then (T + M) % W else T

/-- `step_ok`'s hypotheses, with the values public. -/
def SPre (p : SPub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧ p.X < p.M ∧
    wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.M = p.R

theorem GoodL.congr {L : Lay} {s t : State} (h : GoodL L s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : GoodL L t :=
  ⟨⟨h.1.scr.congr hw, hdi.trans h.1.rdi, hm ▸ h.1.hdr⟩, h.2⟩

theorem SPre.congr {p : SPub} {s t : State} (h : SPre p s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : SPre p t := by
  obtain ⟨hg, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨GoodL.congr hg hm hw hdi, h1, h2, h3, hm ▸ h4, hm ▸ h5, hm ▸ h6, hm ▸ h7, h8, hm ▸ h9⟩

/-- After a step's loads. -/
def SB (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r8 = off p.L.B (slot p.L.w aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
    t.gpr .rbp = off p.L.B (slot p.L.w aTmp)

theorem pins_SB : Pins SB [.rbx, .r10, .r8, .r12, .rbp, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

theorem sb_ok {p : SPub} {s : State} (h : SPre p s) : WP isa (.block R2Words.bases) s (SB p) :=
  WP.mono (R2w.stepBases_ok h.1) fun t ⟨h1, h2, h3, h4, h5, hm, k⟩ =>
    ⟨SPre.congr h hm k.2.2 (k.gpr (by decide)), h1, h2, h3, h4, h5⟩

/-- After `q̂`. -/
def SQ (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rcx = BitVec.ofNat 64 p.q

theorem sq_ok {p : SPub} {s : State} (h : SB p s) : WP isa (.block R2Words.quot) s (SQ p) := by
  obtain ⟨hp, hbx, h10, _, h12, hbp⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, _, hw', hd, hv, hX, hM, hXM, _⟩ := hp'
  have hs := hg.1.scr
  have hZ := hg.2
  have hn := hs.nowrap
  have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  have hsv := slot_le (w := p.L.w) (show aTmp < 8 by decide)
  have hu := R2w.top_le (by omega) (hX ▸ hM ▸ hXM)
  refine WP.mono (R2w.quot_ok hs hbx h10 h12 hbp (by omega) (by omega) (by omega) (by omega) hu hd hv)
    fun t ⟨hcx, hm, k⟩ => ⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
      (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, ?_⟩
  rw [hcx, word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - 1 < p.L.w by omega),
    word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - 2 < p.L.w by omega),
    word_of_wv s.mem p.L.B (slot p.L.w aN) p.L.w (show p.L.w - 1 < p.L.w by omega), hX, hM]
  rfl

/-- At the start of the pass. -/
def SH (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rsi = off p.L.B (slot p.L.w aAcc) ∧
    t.gpr .rdx = BitVec.ofNat 64 p.q ∧ t.gpr .r8 = 0 ∧ t.gpr .r9 = 0 ∧ t.gpr .r14 = 0 ∧ t.gpr .r15 = 0

theorem sh_ok {p : SPub} {s : State} (h : SQ p s) : WP isa (.block mulHead) s (SH p) := by
  obtain ⟨hp, hbx, h10, h12, hcx⟩ := h
  have hg := hp.1
  have hhd := hdr_lt_slot p.L.w 0 (show sArr aAcc < 32 by decide)
  have hs0 := slot_le (w := p.L.w) (show 0 < 8 by decide)
  have hZ := hg.2
  refine WP.mono (mulHead_ok hg.1.scr hg.1.rdi (hg.1.hdr.harr aAcc (by decide)) (by omega))
    fun t ⟨hdx, hsi, h8, h9, h14, h15, hm, k⟩ => ⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)),
      (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hsi,
      hdx.trans hcx, h8, h9, h14, h15⟩

theorem pins_SH : Pins SH [.rbx, .rsi, .r12, .r15, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.2.2.2.2.2, h₂.2.2.2.2.2.2.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

/-- Before a `fix`, with `t = V`. -/
def SF (V : Nat) (p : SPub) (t : State) : Prop :=
  GoodL p.L t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧
    wv t.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) = V ∧ wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M

/-- `T` from `T + q R ≡ V`. -/
theorem t_eq {T q R W V : Nat} (hT : T < W) (hR : R ≤ W) (h : (T + q * R) % W = V % W) :
    T = (V + q * (W - R)) % W := by
  have e : (T + q * R + q * (W - R)) % W = (V + q * (W - R)) % W := by
    rw [Nat.add_mod (T + q * R), h, ← Nat.add_mod]
  rw [Nat.add_assoc, ← Nat.mul_add, show R + (W - R) = W by omega, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hT] at e
  exact e

theorem sf_ok {p : SPub} {s : State} (h : SH p s) :
    WP isa (.seq (.loop (.block tile) .ne) (.block mulTop)) s (SF p.t1 p) := by
  obtain ⟨hp, hbx, h10, h12, hsi, hdx, h8, h9, h14, h15⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, hw4, hw', _, _, hX, hM, hXM, hC⟩ := hp'
  have hs := hg.1.scr
  have hZ := hg.2
  have hn := hs.nowrap
  have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  have hsa := slot_le (w := p.L.w) (show aAcc < 8 by decide)
  have sXA := slot_sep (w := p.L.w) (show aR2 ≠ aAcc by decide)
  have sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
  have hq : p.q < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  refine WP.mono (mulBody_ok (N := p.L.w / 4) hs hbx hsi h12 h8 h9 h14 h15 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun t ⟨hv, ho, k⟩ => ?_
  have hM' : wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M := by rw [ho.wv (by omega) (by omega), hM]
  have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega)
  refine ⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩,
    (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hw, hw', ?_, hM'⟩
  rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, hX, show wv s.mem p.L.B (slot p.L.w aAcc) p.L.w = p.R - p.M by
    omega] at hv
  unfold SPub.t1
  exact t_eq (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega)) hv

theorem pins_SF (V : SPub → Nat) : Pins (fun p => SF (V p) p) [.rbx, .r10, .r12, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.1.1.rdi, h₂.1.1.rdi]

/-- With the sign of `t` in `CF`. -/
def SFc (V : SPub → Nat) (p : SPub) (t : State) : Prop :=
  SF (V p) p t ∧ t.cf = some (decide (p.W / 2 ≤ V p))

theorem fixV_lt {W M T : Nat} (hW : 0 < W) (hT : T < W) : fixV W M T < W := by
  unfold fixV; split
  · exact Nat.mod_lt _ hW
  · exact hT

/-- `fix` leaks the same in runs with the same `t`, which it makes `fixV`. -/
theorem fix_ct (V : SPub → Nat) :
    RelCT isa (Two fun p => SF (V p) p) fix (Two fun p => SF (fixV p.W p.M (V p)) p) := by
  unfold fix
  refine RelCT.seq (two_piece (Ψ := SFc V) _ (pins_SF V) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    have hs := hg.1.scr
    have hn := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hea : s.ea (ix .rbx .r12) = off p.L.B (slot p.L.w aR2 + 8 * p.L.w) := ea_ix0 s hbx h12
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (2 ^ 63 ≤
        (word s.mem p.L.B (slot p.L.w aR2 + 8 * p.L.w)).toNat)) ∧ t.mem = s.mem) (by
      xrun [hea, hs.ld (show slot p.L.w aR2 + 8 * p.L.w + 8 ≤ p.L.Z by omega), top_cf]) rfl)
      fun t ⟨⟨hc, hm⟩, k⟩ => ⟨⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
        (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hw, hw', hm ▸ hT, hm ▸ hM⟩, ?_⟩
    rw [hc, ← hT]
    congr 1
    exact decide_eq_decide.mpr (R2w.top_half _ _ _ _).symm
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · refine (two_piece (Ψ := fun p => SF (fixV p.W p.M (V p)) p) _ (fun p s₁ s₂ h₁ h₂ => pins_SF V p s₁ s₂ h₁.1.1 h₂.1.1)
      (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
    obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    simp only [eval, hc, Option.some.injEq, decide_eq_true_eq] at hb
    have hs := hg.1.scr
    have hn := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧ t.mem = s.mem)
      (by xrun [hbx]) rfl) fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_)
    refine WP.mono (R2w.addBack_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h10) h8
      ((k₁.gpr (by decide)).trans h12) (by omega) (by omega) (by omega) (by omega) (by omega))
      fun t ⟨c, hv, ho, k⟩ => ?_
    simp only [hm₁, ← R2w.top_half, hT, hM] at hv
    simp only [hb, ↓reduceIte] at hv
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem := by
      rw [← hm₁]; exact Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega)
    have kk := k₁.trans k
    refine ⟨⟨⟨hs.congr (k.2.2.trans k₁.2.2), (kk.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩,
      (kk.gpr (by decide)).trans hbx, (kk.gpr (by decide)).trans h10, (kk.gpr (by decide)).trans h12, hw, hw', ?_,
      by rw [ha.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hM⟩
    have hlt := wv_lt t.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
    unfold fixV
    simp only [hb, ↓reduceIte]
    cases c
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
      rw [← hv, Nat.mod_eq_of_lt hlt]
    · simp only [Bool.toNat_true, Nat.mul_one] at hv
      rw [← hv, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · refine (two_piece (Ψ := fun p => SF (fixV p.W p.M (V p)) p) [] (fun _ _ _ _ _ _ h => nomatch h)
      (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => WP.block_nil ?_).mono (fun _ _ h => h) fun _ _ h => h
    simp only [eval, hc, Option.some.injEq, decide_eq_false_iff_not] at hb
    obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    exact ⟨hg, hbx, h10, h12, hw, hw', by unfold fixV; simp only [hb, ↓reduceIte]; exact hT, hM⟩

/-- The pass: `t` leaks nothing but its addresses. -/
theorem mulSub_ct : RelCT isa (Two SQ) mulSub (Two (fun p => SF p.t1 p)) := by
  unfold mulSub
  refine RelCT.seq (two_piece (Ψ := SH) [.rdi] (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide)
    fun _ _ h => sh_ok h) ?_
  exact two_post (two_taint _ pins_SH (by taint_decide)) fun _ _ h => sf_ok h

/-- A step leaks the same in runs with the same working space, `x` and `m`. -/
theorem step_ct : RelCT isa (Two SPre) step fun _ _ => True := by
  rw [show step = .seq (.block R2Words.bases) (.seq (.block R2Words.quot) (.seq mulSub (.seq fix fix))) from rfl]
  refine RelCT.seq (two_piece (Ψ := SB) [.rdi] (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide)
    fun _ _ h => sb_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := SQ) _ pins_SB (by taint_decide) fun _ _ h => sq_ok h) ?_
  refine RelCT.seq mulSub_ct (RelCT.seq (fix_ct (fun p => p.t1)) ?_)
  exact (fix_ct (fun p => fixV p.W p.M p.t1)).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The steps -/

/-- The public data of `steps`: the working space, the count and `m`. -/
structure StPub where
  L : Lay
  c : Nat
  M : Nat

/-- `x` after `j` steps from `R - m`. -/
def StPub.X (p : StPub) (j : Nat) : Nat := (2 ^ (64 * p.L.w) - p.M) * 2 ^ (64 * j) % p.M

/-- What `steps` keeps, after `j` steps. -/
def StepsAt (p : StPub) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (T : Nat), StepsInv σ p.L.B p.L.Z p.L.w p.L.minv p.c (2 ^ (64 * p.L.w) - p.M) p.M T j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧ p.c < 2 ^ 31 ∧ 0 < p.M ∧ 2 ^ 63 ≤ T

theorem stepsAt_good {p : StPub} {j : Nat} {t : State} (h : StepsAt p j t) : GoodL p.L t :=
  let ⟨_, _, hI, hZ, _⟩ := h; ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

theorem stepsAt_pre {p : StPub} {j : Nat} {t : State} (h : StepsAt p j t) :
    SPre ⟨p.L, p.X j, p.M⟩ t := by
  obtain ⟨_, T, hI, hZ, hw, hw4, hw', _, hM, hT⟩ := h
  exact ⟨⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩, hw, hw4, hw', by rw [hI.top]; exact hT, by rw [hI.rcp, hI.top], hI.xv,
    hI.nv, Nat.mod_lt _ hM, hI.acc⟩

/-- `steps`' hypotheses. -/
def StepsPre (p : StPub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧ 1 ≤ p.c ∧ p.c < 2 ^ 31 ∧
    s.gpr .rcx = BitVec.ofNat 64 p.c ∧ 2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.M ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    2 ^ (64 * p.L.w) - p.M < p.M ∧ wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.M = 2 ^ (64 * p.L.w)

/-- `steps` leaks the same in runs with the same working space, count and `m`. -/
theorem steps_ct : RelCT isa (Two StepsPre) steps (Two fun p s => StepsAt p p.c s) := by
  rw [steps_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ StepsAt p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨hg, hw, hw4, hw', hc1, hc', hcx, hT, hv, hX, hN, hO, hC⟩
    have hM : 0 < p.M := by omega
    have hO' : wv s.mem p.L.B (slot p.L.w aR2) p.L.w < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by
      rw [hX, hN]; exact hO
    refine WP.mono (stepsStart_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hcx hO' hv (by rw [hN]; exact hC))
      fun t hI => ⟨by omega, s, _, ?_, hg.2, hw, hw4, hw', hc', hM, hT⟩
    rw [hX, hN] at hI; exact hI
  refine two_loop (Φ := StepsAt) (fun p => p.c) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun (q : StPub × Nat) s => GoodL q.1.L s)
      ((two_map (fun q : StPub × Nat => (⟨q.1.L, q.1.X q.2, q.1.M⟩ : SPub)) (fun _ _ h => stepsAt_pre h.2)
        step_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_good q.1.L s₁ s₂ h₁ h₂) (by taint_decide))
    rintro ⟨p, j⟩ s ⟨hj, h⟩
    have hp := stepsAt_pre h
    obtain ⟨hg, hw, hw4, hw', hd, hv, hX, hN, hXM, hC⟩ := hp
    exact WP.mono (step_ok hg hw hw4 hw' hd hv (by rw [hX, hN]; exact hXM) (by rw [hN]; exact hC))
      fun t ⟨hg', _⟩ => hg'
  · rintro p j s hj ⟨σ, T, hI, hZ, hw, hw4, hw', hc', hM, hT⟩
    exact WP.mono (stepIter_ok hZ hw hw4 hw' hc' hM hT hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, T, hI', hZ, hw, hw4, hw', hc', hM, hT⟩,
        fun e => e ▸ ⟨σ, T, hI', hZ, hw, hw4, hw', hc', hM, hT⟩⟩

/-! ## `fast` -/

/-- What `fast` keeps from `R - m` on, `x = R - m`. -/
def FX (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.L.w % 4 = 0 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.N ∧ 2 ^ (64 * p.L.w) - p.N < p.N

/-- After `R - m`. -/
def FX2 (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ s.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- Before the copy into the accumulator. -/
def FX3 (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ s.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧ s.gpr .rbx = off p.L.B (slot p.L.w aAcc) ∧
    s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- With `mc = R - m` in the accumulator. -/
def FXA (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.N = 2 ^ (64 * p.L.w) ∧
    s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- Before `v`. -/
def FX5 (p : R2Pub) (s : State) : Prop := FXA p s ∧ s.gpr .r8 = off p.L.B (slot p.L.w aTmp)

/-- After `v`. -/
def FX6 (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.L.w % 4 = 0 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.N ∧ 2 ^ (64 * p.L.w) - p.N < p.N ∧
    wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.N = 2 ^ (64 * p.L.w) ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64

theorem pins_FX2 : Pins FX2 [.rbx, .r10, .r12, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

theorem pins_FX3 : Pins FX3 [.r8, .rbx, .r12] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.2, h₂.2.2.2.2]

theorem pins_FX5 : Pins FX5 [.r10, .r12, .r8] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.1.2.2.1, h₂.1.2.2.1]
  · rw [h₁.1.2.2.2, h₂.1.2.2.2]
  · rw [h₁.2, h₂.2]

theorem FX.congr {p : R2Pub} {s t : State} (h : FX p s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : FX p t := by
  obtain ⟨hg, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨GoodL.congr hg hm hw hdi, h1, h2, h3, hm ▸ h4, hm ▸ h5, hm ▸ h6, h7⟩

/-- `fast` leaks the same in runs that agree on `m`. -/
theorem fast_ct : RelCT isa (Two R2w.FPre) fast fun _ _ => True := by
  rw [fast_eq]
  -- The loads.
  refine RelCT.seq (two_piece (Ψ := R2w.F1) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega)
    refine WP.mono (WP.keep [.rbx, .r10, .r12, .r8, .rbp] (Q := fun t =>
        t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .r8 = off p.L.B (slot p.L.w aTmp) ∧ t.gpr .rbp = mask false ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
        hl (sArr aTmp) (by decide), hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aN (by decide), hg.1.hdr.hw,
        hg.1.hdr.harr aTmp (by decide)]) rfl)
      fun t ⟨⟨hbx, h10, h12, h8, hbp, hm⟩, k⟩ => ⟨⟨?_, h.2⟩, hbx, hbp, h8⟩
    obtain ⟨⟨hg, hw, hw', hN, hinv, -, -, hodd, hlo⟩, -⟩ := h
    exact ⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), hw, hw', hm ▸ hN, hm ▸ hinv, h12, h10, hodd, hlo⟩
  -- `R - m`.
  refine RelCT.seq (two_piece (Ψ := FX2) _ R2w.pins_F1 (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩, hT, h4⟩, hbx, hbp, h8⟩
    obtain ⟨hT', -⟩ := R2Pre.top ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    have hN0 : 0 < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by rw [hN]; omega
    have hng := R2w.neg_ok hs hbx h10 h12 hbp (by omega) (by omega) (by omega) (by omega) (by omega) hN0
    refine WP.mono hng fun t ⟨hx, ho, k⟩ => ?_
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega)
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by omega
    have hhalf : 2 ^ (64 * p.L.w) < 2 * p.N := by
      have e : p.N = wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1) +
          2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
        rw [← hN, show p.L.w = (p.L.w - 1) + 1 by omega, wv_succ, show p.L.w - 1 + 1 - 1 = p.L.w - 1 by omega]
      have hp : 2 ^ (64 * p.L.w) = 2 * (2 ^ (64 * (p.L.w - 1)) * 2 ^ 63) := by
        rw [← Nat.pow_add, show 64 * p.L.w = 1 + (64 * (p.L.w - 1) + 63) by omega, Nat.pow_add, Nat.pow_one]
      rw [hT'] at e
      have hle := Nat.mul_le_mul_left (2 ^ (64 * (p.L.w - 1))) hT
      have hev : 2 ^ (64 * (p.L.w - 1)) * 2 ^ 63 % 2 = 0 := by
        rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
      omega
    have hNR : p.N < 2 ^ (64 * p.L.w) := hN ▸ wv_lt _ _ _ _
    refine ⟨⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, by omega, hw', h4,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ho.word (by omega) (by omega), hT']; exact hT, by rw [hx, hN], by omega⟩,
      (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `mc`'s bases.
  refine RelCT.seq (two_piece (Ψ := FX3) _ pins_FX2 (by taint_decide) ?_) ?_
  · rintro p s ⟨hx, hbx, h10, h12⟩
    have hg := hx.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega)
    refine WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧
        t.gpr .rbx = off p.L.B (slot p.L.w aAcc) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aAcc) (by decide), hg.1.hdr.harr aAcc (by decide), hbx]) rfl)
      fun t ⟨⟨h8, hb, hm⟩, k⟩ => ⟨FX.congr hx hm k.2.2 (k.gpr (by decide)), h8, hb,
        (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `mc := x`.
  refine RelCT.seq (two_post (Ψ := FXA) (two_taint _ pins_FX3 (by taint_decide)) ?_) ?_
  · rintro p s ⟨hx, h8, hbx, h10, h12⟩
    have hx' := hx
    obtain ⟨hg, hw, hw', h4, hN, hT, hX, hO⟩ := hx'
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have hsa := slot_le (w := p.L.w) (show aAcc < 8 by decide)
    have sXA := slot_sep (w := p.L.w) (show aR2 ≠ aAcc by decide)
    have sMA := slot_sep (w := p.L.w) (show aN ≠ aAcc by decide)
    unfold R2Words.copyBack
    refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off p.L.B (slot p.L.w aR2) ∧ t.mem = s.mem)
      (by xrun [h8]) rfl) fun t₁ ⟨⟨hsi, hm₁⟩, k₁⟩ => ?_)
    have hs₁ := hs.congr k₁.2.2
    have hsepw : ∀ j < p.L.w, ∀ b < 8, ofs p.L.B (off p.L.B (slot p.L.w aR2 + 8 * j) + BitVec.ofNat 64 b) <
        slot p.L.w aAcc ∨ slot p.L.w aAcc + 8 * p.L.w ≤ ofs p.L.B (off p.L.B (slot p.L.w aR2 + 8 * j) +
          BitVec.ofNat 64 b) := fun j hj b hb => by
      rw [ofs_off p.L.B (by omega)]; omega
    refine WP.mono (copyWords_ok (S := p.L.B) (D := p.L.B) hsi ((k₁.gpr (by decide)).trans hbx)
      ((k₁.gpr (by decide)).trans h12) (by omega) (by omega) (by omega) (fun j hj => hs₁.ld (by omega))
      (fun j hj => hs₁.st (by omega)) hsepw) fun t ⟨hc, _, ho, k⟩ => ?_
    rw [hm₁] at hc ho
    have ha : Arrays p.L.B p.L.w [aAcc] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega)
    have kk := k₁.trans k
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by omega
    have hNR : p.N < 2 ^ (64 * p.L.w) := hN ▸ wv_lt _ _ _ _
    refine ⟨⟨⟨⟨hs.congr (k.2.2.trans k₁.2.2), (kk.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ho.word (by omega) (by omega)]; exact hT,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hX, hO⟩,
      by rw [hc, hX]; omega, (kk.gpr (by decide)).trans h10, (kk.gpr (by decide)).trans h12⟩
  -- `v`'s bases.
  refine RelCT.seq (two_piece (Ψ := FX5) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨hx, hc, h10, h12⟩
    have hg := hx.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega)
    refine WP.mono (WP.keep [.rbx, .r8] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aTmp) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide),
        hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aTmp (by decide)]) rfl)
      fun t ⟨⟨h8, hm⟩, k⟩ => ⟨⟨FX.congr hx hm k.2.2 (k.gpr (by decide)), hm ▸ hc, (k.gpr (by decide)).trans h10,
        (k.gpr (by decide)).trans h12⟩, h8⟩
  -- `v`.
  refine RelCT.seq (two_piece (Ψ := FX6) _ pins_FX5 (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨hg, hw, hw', h4, hN, hT, hX, hO⟩, hc, h10, h12⟩, h8⟩
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have hsv := slot_le (w := p.L.w) (show aTmp < 8 by decide)
    have hsa := slot_le (w := p.L.w) (show aAcc < 8 by decide)
    have sXV := slot_sep (w := p.L.w) (show aR2 ≠ aTmp by decide)
    have sMV := slot_sep (w := p.L.w) (show aN ≠ aTmp by decide)
    have sAV := slot_sep (w := p.L.w) (show aAcc ≠ aTmp by decide)
    refine WP.mono (R2w.recip_ok hs h10 h12 h8 (by omega) (by omega) (by omega) hT) fun t ⟨hm, k⟩ => ?_
    have o : Outside p.L.B (slot p.L.w aTmp) 8 s.mem t.mem := by rw [hm]; exact writeW_outside _ _ _ (by omega)
    have ha : Arrays p.L.B p.L.w [aTmp] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega)
    have hvlt : (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 < 2 ^ 64 := by
      have : (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat < 2 ^ 65 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      omega
    have hT₁ : word t.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1)) =
        word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1)) := o.word (by omega) (by omega)
    refine ⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
      by rw [o.wv (by omega) (by omega)]; exact hN, by rw [hT₁]; exact hT,
      by rw [o.wv (by omega) (by omega)]; exact hX, hO, by rw [o.wv (by omega) (by omega)]; exact hc, ?_⟩
    rw [hT₁, hm, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  -- The count.
  refine RelCT.seq (two_piece (Ψ := fun p s => FX6 p s ∧ s.gpr .rcx = BitVec.ofNat 64 p.L.w) _
    (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega)
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 p.L.w ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl sW (by decide), hg.1.hdr.hw]) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨?_, hcx⟩
    obtain ⟨hg, hw, hw', h4, hN, hT, hX, hO, hc, hv⟩ := h
    exact ⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), hw, hw', h4, hm ▸ hN, hm ▸ hT, hm ▸ hX, hO, hm ▸ hc, hm ▸ hv⟩
  -- The steps.
  refine (two_map (fun p : R2Pub => (⟨p.L, p.L.w, p.N⟩ : StPub)) (fun p s h => ?_) steps_ct).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨⟨hg, hw, hw', h4, hN, hT, hX, hO, hc, hv⟩, hcx⟩ := h
  exact ⟨hg, hw, h4, hw', show 1 ≤ p.L.w by omega, show p.L.w < 2 ^ 31 by omega, hcx, hT, hv, hX, hN, hO, hc⟩

/-! ## The choice -/

/-- `choice` leaks the same in runs that agree on `m`. -/
theorem choice_ct (M : Mont) : RelCT isa (Two R2Pre) (R2Adx.choice M.mm) fun _ _ => True := by
  unfold R2Adx.choice
  refine RelCT.seq (two_piece (Ψ := R2w.R2t) _ pins_r2Pre (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hT, -⟩ := h.top
    have hn := h.1.1.scr.nowrap
    have := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (2 ^ 63 ≤ p.top ∧ p.L.w % 4 = 0)) ∧
        t.mem = s.mem) (by
      unfold R2Words.fastTest
      xrun [State.ea, ix, addrm8 h.2.2.2.2.2.2.1 h.2.2.2.2.2.1 (by have := h.2.1; omega),
        h.1.1.scr.ld (show slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega)]
      rw [h.2.2.2.2.2.1]
      refine (R2w.fastFlag _ (by have := h.2.2.1; omega)).trans ?_
      rw [← hT]) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨?_, hz⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map id (fun p s ⟨⟨h, hz⟩, hc⟩ => by
      simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at hc
      exact ⟨h, hc.1, hc.2⟩) fast_ct
  · rw [R2w.old_eq]
    exact two_map id (fun p s h => h.1.1) (r2_ct M)

end VG.Proof.Bignum.X86_64.R2ax
