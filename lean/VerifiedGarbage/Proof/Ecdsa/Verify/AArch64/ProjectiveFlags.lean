import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Final

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

theorem projective_mov (s : State) (r : Reg) :
    WP isa (.block [.addImm .x r .x2 0]) s fun t => t.gpr r = s.gpr .x2 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (0 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

theorem projective_combine (s : State) :
    WP isa (.block [.logic .and .x .x2 .x2 .x6, .logic .orr .x .x2 .x2 .x4]) s fun t =>
      t.gpr .x2 = (s.gpr .x2 &&& s.gpr .x6) ||| s.gpr .x4 ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', ↓reduceIte, reduceCtorEq]
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  simp only [RegUpd.gpr_write, hq, ↓reduceIte]

theorem projective_mask_or (p q : Prop) [Decidable p] [Decidable q] :
    mask p ||| mask q = mask (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [mask, hp, hq]

/-- The public-coordinate comparisons leave their combined mask in `x2`. -/
theorem projectiveMatch_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveMatch c)) s fun t =>
      t.gpr .x2 = mask (sv c base s W = 0 ∨
        (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) ∧
      Keeps [.x1, .x2, .x4, .x5, .x6, .x7, .x16] s t := by
  have hz := hc.n0
  have hl := hc.n10
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectiveMatch]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs hz (sl_le c hl (i := W) (by decide)) (sl_mod8 c W)) fun s₁ ⟨e₁,k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (projective_mov s₁ .x4) fun s₂ ⟨e₂,k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ltN_ok c hs₂ hz (sl_le c hl (i := K) (by decide))
    (sl_le c hl (i := MN) (by decide)) (sl_mod8 c K) (sl_mod8 c MN)) fun s₃ ⟨e₃,k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (projective_mov s₃ .x6) fun s₄ ⟨e₄,k₄⟩ => ?_
  have hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs₄ hz (sl_le c hl (i := XN) (by decide)) (sl_mod8 c XN)) fun s₅ ⟨e₅,k₅⟩ => ?_
  refine WP.mono (projective_combine s₅) fun s₆ ⟨e₆,k₆⟩ => ⟨?_, ?_⟩
  · rw [e₆, e₅, k₅.gpr .x6 (by decide), e₄, e₃, k₅.gpr .x4 (by decide),
      k₄.gpr .x4 (by decide), k₃.gpr .x4 (by decide), e₂, e₁,
      k₄.mem, k₃.mem, k₂.mem, k₁.mem, mask_and, projective_mask_or]
    simp only [sv, or_comm, and_comm]
  · exact (k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans
      ((k₃.mono (by sub_regs)).trans ((k₄.mono (by sub_regs)).trans
        ((k₅.mono (by sub_regs)).trans (k₆.mono (by sub_regs))))))


/-- The comparisons, nonzero test, return value and ABI restoration. -/
theorem projectiveChecks_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g VG.Impl.Ecdsa.AArch64.Cfg.saved s.mem)
    (A : Prop) [Decidable A] (hf : word s.mem base (c.sl FLAG) = mask A) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveChecks c)) s fun t =>
      (∀ r ∈ VG.Impl.Ecdsa.AArch64.Cfg.saved.map Prod.fst, t.gpr r = g r) ∧
      (t.gpr .x0).setWidth 32 = if A ∧ sv c base s RZ ≠ 0 ∧
        (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hflag : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectiveChecks]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (projectiveMatch_ok hc hs) fun s₁ ⟨e₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (andFlag_ok c hs₁ hflag (sl_mod8 c FLAG)) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₂ h0 (sl_le c h7 (i := RZ) (by decide)) hflag
    (sl_mod8 c RZ) (sl_mod8 c FLAG)) fun s₃ ⟨e₃,k₃,O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U : Unch base [(c.sl FLAG, 8)] s.mem s₃.mem := by
    rw [← k₁.mem]
    exact (O₂.unch.trans O₃.unch).mono (by intro w hw; simpa using hw)
  have saved := Saved.unch hsv (fun w hw => by
    rw [List.mem_singleton.mp hw]
    exact sl_ge64 c FLAG) U
  have z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := by
    rw [show wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s₁ RZ from
      sv_flag O₂ h0 h7 hs.nowrap (by decide) (by decide)]
    show wordsVal s₁.mem base (c.sl RZ) c.n = _
    rw [k₁.mem]
  have flag₃ : word s₃.mem base (c.sl FLAG) =
      mask (A ∧ sv c base s RZ ≠ 0 ∧
        (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))) := by
    rw [e₃,e₂,k₁.mem,hf,e₁,z₂,mask_and,mask_and]
    simp only [and_left_comm, and_comm]
  refine WP.mono (vfinish_ok hc hs₃ saved (decide (A ∧ sv c base s RZ ≠ 0 ∧
      (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)))) (by simpa only [mask, decide_eq_true_eq] using flag₃))
    fun t ⟨ret,keep⟩ => ⟨keep,?_⟩
  simpa only [decide_eq_true_eq] using ret

end VG.Proof.Ecdsa.Verify.AArch64
