import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Points

/-!
# ECDSA verification on x86 (32-bit): `x` and the result

As on AArch64 (`Proof/Ecdsa/Verify/AArch64/Final.lean`).

`vtail_ok`: from what `points_ok` leaves, the signature's power gives
`Z^(p-2)`, and `final` computes `x = X Z^(p-2)` out of Montgomery's form,
`x R mod n` and `x R - r R mod n`, ands the masks of `Z ≠ 0` and of that
difference being zero (`x ≡ r` modulo `n`) into the flag, returns its low
bit and restores the callee-saved registers (`vfinish_ok`, the signature's
`tail_ok`). It writes only the working space.
-/

namespace VG.Proof.Ecdsa.Verify.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdsa.Verify.X86 (RM' XN W)

variable {c : Cfg}

theorem vfinish_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.finish c =
    .mov .ecx (.mem (sc (c.sl FLAG))) ::
      (([.mov .eax (.reg .ecx), .alu .and .eax (.imm 1)] : List Instr) ++ Cfg.restore) := rfl

/-- The return value and the callee-saved registers. -/
theorem vfinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.finish c)) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧ s'.gpr .esp = s.gpr .esp := by
  have hF := sl_le c hc.n10 (i := FLAG) (by decide)
  have := hc.n0
  have hsz : size = 8192 := rfl
  rw [vfinish_eq]
  refine wp_movS (readSrc_sc hs (d := c.sl FLAG) (by omega)) fun s₁ u₁ _ => ?_
  refine WP.mono (tail_ok (hs.of_keeps u₁.keeps (by decide)) (fun rd hrd => by rw [u₁.mem]; exact hsv rd hrd) b
    (by rw [u₁.gpr, ← flagW, hf])) fun s' ⟨hm, eax, saved, others⟩ =>
      ⟨by rw [hm, u₁.mem], eax, saved, by rw [others _ (by decide), u₁.other _ (by decide)]⟩

/-- `[o] = ([a] - [b]) mod m`, on slots. -/
theorem slSub_ok {M : Mod} {m : Nat} (hMn : M.n = c.n) (hmo : M.mo = c.sl MP ∨ M.mo = c.sl MN)
    (hMt : M.tmp = c.sl TMP) (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hot : o ≠ TMP) (hA : sv c base s a < m) (hB : sv c base s b < m) :
    WP isa (.block (sub M c.wk (c.sl o) (c.sl a) (c.sl b))) s fun s' => OpKeep M base c.wk (c.sl o) s s' ∧
      sv c base s' o = (sv c base s a + m - sv c base s b) % m := by
  have := sub_ok hs hM (slLay hMn hmo hMt h7 ho ha hb hot) (by rw [hMn]; exact hA) (by rw [hMn]; exact hB)
  rw [hMn] at this
  exact this

theorem final_eq (c : Cfg) : Impl.Ecdsa.Verify.X86.Cfg.final c =
    .seq (mul c.MP' c.wk (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mul c.MP' c.wk (c.sl X) (c.sl XM) (c.sl ONE))
    (.seq (mul c.MN' c.wk (c.sl XN) (c.sl X) (c.sl R2N))
    (.seq (.block (sub c.MN' c.wk (c.sl W) (c.sl XN) (c.sl RM')))
      (.block (c.checkNonzero (c.sl RZ) ++ (Impl.Ecdh.X86.Cfg.checkZero c (c.sl W) ++
        Impl.Ecdsa.Verify.X86.Cfg.finish c)))))) := by
  simp only [Impl.Ecdsa.Verify.X86.Cfg.final, progs, List.append_assoc]

/-- The slots `vtail_ok` writes. -/
abbrev finW : List Nat := [ACC, PT, TMP, XM, X, XN, W]

/-- `Z^(p-2)`, `x`, the last checks and the result. -/
theorem vtail_ok (hc : CfgOk c) {s₀ : State} {base : Addr}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State} (hP : Pts c s₀ base Q₁ Q₂ s) :
    WP isa (.seq (pow c.powP c.wk) (Impl.Ecdsa.Verify.X86.Cfg.final c)) s fun s' =>
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      Unch base [(0, size)] s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .eax = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hn3 := hc.n_ge
  have F := hP.fixed
  have hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) (powWkP hc) hpR hP.scr
    (modP_of hc F.mp) hP.rz_lt F.onep hP.t₁ (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega))
    fun s₁ ⟨K₁, U₁, lt₁, v₁⟩ => ?_)
  rw [powWxP_eq, accLen_MP'] at U₁
  have hs₁ := hP.scr.of_keeps K₁ (by decide)
  have F₁ := F.unch h7 hn (fixedOk_slWk (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁ h7 hn hi (apart_slWk hi hl)
  rw [final_eq]
  -- `XM = X · ACC`.
  have hM₁ := modP_of hc F₁.mp
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₁ hM₁ (o := XM) (a := RX) (b := ACC)
    (by decide) (by decide) (by decide) (by decide) lt₁) fun s₂ ⟨k₂, _, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have M₂ := hM₁.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₂ hi h₁ h₂
  -- `X = XM · 1`.
  have one₂ : sv c base s₂ ONE = 1 := (v₂ (by decide) (by decide) (by decide)).trans F₁.one
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₂ M₂ (o := X) (a := XM) (b := ONE)
    (by decide) (by decide) (by decide) (by decide) (by rw [one₂]; omega)) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have v₃ : ∀ {i}, i < 45 → i ≠ X → i ≠ TMP → sv c base s₃ i = sv c base s₂ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₃ hi h₁ h₂
  have x₃ : Fin.ofNat c.C.p (sv c base s₃ X) =
      tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := by
    have acc₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RZ) ^ (c.C.p - 2) := v₁
    rw [toM_one_mul hpR (by rw [e₃, one₂]), toM_mul hpR e₂, acc₁]
    show toM _ _ (sv c base s₁ RX) * _ = toM _ _ (sv c base s RX) * toM _ _ (sv c base s RZ) ^ _
    rw [e₁ (by decide) (by decide)]
  -- `XN = x R mod n`, `W = XN - r R mod n`.
  have hMN₃ := modN_of hc (show wordsVal s₃.mem base (c.sl MN) c.n = c.C.n from
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.mn)))
  have r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n :=
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.r2n))
  refine WP.seq (WP.mono (slMul_ok (MN'_n c) (.inr rfl) rfl h7 hs₃ hMN₃ (o := XN) (a := X) (b := R2N)
    (by decide) (by decide) (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega)))
    fun s₄ ⟨k₄, lt₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  have M₄ := hMN₃.keepX86 (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide)
  have v₄ : ∀ {i}, i < 45 → i ≠ XN → i ≠ TMP → sv c base s₄ i = sv c base s₃ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₄ hi h₁ h₂
  have rm₄ : sv c base s₄ RM' = sv c base s RM' := by
    rw [v₄ (by decide) (by decide) (by decide), v₃ (by decide) (by decide) (by decide),
      v₂ (by decide) (by decide) (by decide), e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (slSub_ok (MN'_n c) (.inr rfl) rfl h7 hs₄ M₄ (o := W) (a := XN) (b := RM')
    (by decide) (by decide) (by decide) (by decide) lt₄ (by rw [rm₄]; exact hP.rm_lt)) fun s₅ ⟨k₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr hs₄
  have v₅ : ∀ {i}, i < 45 → i ≠ W → i ≠ TMP → sv c base s₅ i = sv c base s₄ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₅ hi h₁ h₂
  have w₅ : sv c base s₅ W = 0 ↔ Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀) := by
    have hlt : sv c base s₅ W < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega)
    rw [← toM_eq_zero_iff hnR hlt, e₅, toM_sub (by rw [rm₄]; have := hP.rm_lt; omega), rm₄, hP.rm,
      toM_r2 hnR (by rw [e₄, r2₃])]
    constructor <;> intro h <;> grind
  -- What changed: `finW` and the accumulator.
  have hsub : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ finW) → ∀ w, w ∈ slW c l ∨ w ∈ [(c.wk, 16 * c.n + 4)] →
      w ∈ slWk c finW := fun hl w hw => by
    rcases hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hl i hi))
    · exact List.mem_append_right _ hw
  have U₅ : Unch base (slWk c finW) s.mem s₅.mem :=
    (U₁.trans ((unch_slots (MP'_n c) rfl k₂.unch (l := [XM, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MP'_n c) rfl k₃.unch (l := [X, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MN'_n c) rfl k₄.unch (l := [XN, TMP]) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₅.unch (l := [W, TMP]) (by simp) (by simp)))))).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with hw | hw | hw | hw | hw
      all_goals exact hsub (by decide) w hw
  -- The checks and the result.
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c hs₆ h0 (sl_le c h7 (i := W) (by decide)) hf) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have UW : Unch base (slWk c finW ++ [(c.sl FLAG, 4)]) s.mem s₇.mem := by
    have := U₅.trans (O₆.unch.trans O₇.unch)
    exact this.mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_right _ hw
        · exact List.mem_append_right _ hw
  have F₇ := F.unch h7 hn ((fixedOk_slWk (by decide)).append fixedOk_flag) UW
  have z₅ : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ := by
    show sv c base s₅ RZ = _
    rw [v₅ (by decide) (by decide) (by decide), v₄ (by decide) (by decide) (by decide),
      v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide) (by decide),
      e₁ (by decide) (by decide)]
  have hW₆ : wordsVal s₆.mem base (c.sl W) c.n = sv c base s₅ W :=
    sv_flag O₆ h0 h7 hn (by decide) (by decide)
  have hflag : flagW c base s₇ = mask32 (decide ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
      (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
      Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀)) = true) := by
    rw [f₇, f₆, hW₆, flagW, flag_unch U₅ h7 h0 hn (by decide), ← flagW, hP.flag, z₅, mask32_and, mask32_and]
    simp only [w₅, decide_eq_true_eq, and_assoc]
  refine WP.mono (vfinish_ok hc hs₇ F₇.saved _ hflag) fun s' ⟨hm, ret, saved, esp⟩ =>
    ⟨saved, ?_, ?_, _, lt₃, x₃, ?_⟩
  · rw [esp, k₇.1 _ (by decide), k₆.1 _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide),
      k₃.gpr _ (by decide), k₂.gpr _ (by decide), K₁.1 _ (by decide), hP.esp]
  · rw [hm]
    exact whole_of hP.unch UW (le_append (slWk_le h7 (by decide)) (flag_le h0 h7))
  · rw [ret]
    simp only [decide_eq_true_eq]

end VG.Proof.Ecdsa.Verify.X86
