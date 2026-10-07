import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final

/-! # Masks for the inversion-free x86 ECDSA comparison -/
namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
open VG.Impl.Ecdsa.Verify.X86 (W XN)
variable {c : Cfg}

theorem projective_mask_or (p q : Prop) [Decidable p] [Decidable q] :
    mask32 p ||| mask32 q = mask32 (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [mask32, hp, hq]

/-- Both equalities and the bound on the second lift, as one mask. -/
theorem projectiveMatch_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.projectiveMatch c)) s fun t =>
      t.gpr .edx = mask32 (sv c base s W = 0 ∨
        (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t ∧ t.mem = s.mem := by
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectiveMatch]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (nonzero_ok c hs hc.n0 (sl_le c hc.n10 (i := W) (by decide)))
    fun s₁ ⟨e₁,k₁,m₁⟩ => ?_)
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_logicS (.inr rfl) rfl fun s₂ u₂ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  have k₃ : Keeps [.eax, .ebx, .ecx, .edx] s s₃ := ((k₁.mono (by decide)).widen u₂.keeps).widen u₃.keeps
  refine WP.block_append (WP.mono (ltN_ok c (hs.of_keeps k₃ (by decide)) hc.n0
    (sl_le c hc.n10 (i := K) (by decide)) (sl_le c hc.n10 (i := MN) (by decide))) fun s₄ ⟨e₄,k₄,m₄⟩ => ?_)
  have k₄' := k₃.widen k₄
  refine WP.block_append (WP.mono (nonzero_ok c (hs.of_keeps k₄' (by decide)) hc.n0
    (sl_le c hc.n10 (i := XN) (by decide))) fun s₅ ⟨e₅,k₅,m₅⟩ => ?_)
  refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₇ u₇ => ?_
  refine wp_orS rfl fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₈.gpr, u₇.gpr, u₆.gpr, e₅, u₆.other _ (by decide), k₅.1 _ (by decide), e₄,
      u₇.other _ (by decide), u₆.other _ (by decide), k₅.1 _ (by decide), k₄.1 _ (by decide),
      u₃.gpr, u₂.gpr, e₁, m₄, u₃.mem, u₂.mem, m₁]
    simp only [reduceCtorEq, ite_false, ite_true, mask_not, ne_eq, not_not, mask32_and, projective_mask_or,
      sv, and_comm, or_comm]
  · exact (((k₄'.widen k₅).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps
  · rw [u₈.mem, u₇.mem, u₆.mem, m₅, m₄, u₃.mem, u₂.mem, m₁]

/-- The masks, return value, and restoration change only the flag word. -/
theorem projectiveChecks_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    {g : Reg → BitVec 32} (saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1)
    (A : Prop) [Decidable A] (hf : flagW c base s = mask32 A) :
    WP isa (.block (Impl.Ecdsa.Verify.X86.Cfg.projectiveChecks c)) s fun t =>
      (∀ rd ∈ Cfg.saved, t.gpr rd.1 = g rd.1) ∧ t.gpr .esp = s.gpr .esp ∧
      Unch base [(c.sl FLAG, 4)] s.mem t.mem ∧
      t.gpr .eax = if A ∧ sv c base s RZ ≠ 0 ∧
        (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hflag : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectiveChecks]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (projectiveMatch_ok hc hs) fun s₁ ⟨e₁,k₁,m₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (andFlag_ok c hs₁ hflag) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (checkNonzero_ok c hs₂ h0 (sl_le c h7 (i := RZ) (by decide)) hflag)
    fun s₃ ⟨e₃,k₃,O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have U : Unch base [(c.sl FLAG, 4)] s.mem s₃.mem := by
    rw [← m₁]
    exact (O₂.unch.trans O₃.unch).mono (by intro w hw; simpa using hw)
  have saved₃ : ∀ rd ∈ Cfg.saved, s₃.mem.readW (off base rd.2) 32 = g rd.1 := by
    intro rd hr
    have bound : rd.2 + 4 ≤ 16 := by revert rd; decide
    rw [Unch.readW32 U (fun w hw => by rw [List.mem_singleton.mp hw]; left; rw [sl_eq]; omega) (by omega)]
    exact saved rd hr
  have z₂ : wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ := by
    rw [show wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s₁ RZ from
      sv_flag O₂ h0 h7 hs.nowrap (by decide) (by decide)]
    show wordsVal s₁.mem base (c.sl RZ) c.n = _
    rw [m₁]
  have flag₃ : flagW c base s₃ = mask32 (A ∧ sv c base s RZ ≠ 0 ∧
      (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))) := by
    rw [e₃,e₂,flagW,m₁,← flagW,hf,e₁,z₂,mask32_and,mask32_and]
    simp only [and_left_comm, and_comm]
  refine WP.mono (vfinish_ok hc hs₃ saved₃ (decide (A ∧ sv c base s RZ ≠ 0 ∧
    (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))))
    (by simpa only [decide_eq_true_eq] using flag₃)) fun t ⟨hm,ret,keep,esp⟩ => ?_
  refine ⟨keep, ?_, ?_, ?_⟩
  · rw [esp,k₃.1 _ (by decide),k₂.1 _ (by decide),k₁.1 _ (by decide)]
  · rw [hm]; exact U
  · simpa only [decide_eq_true_eq] using ret

end VG.Proof.Ecdsa.Verify.X86
