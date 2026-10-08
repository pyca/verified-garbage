import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
variable {c : VG.Impl.Ecdsa.X86_64.Cfg}

theorem projectiveMerge_ok (s : State) :
    WP isa (.block [.alu .and .rdx (.reg .r12), .alu .or .rdx (.reg .rbp)]) s fun t =>
      t.gpr .rdx = (s.gpr .rdx &&& s.gpr .r12) ||| s.gpr .rbp ∧ Keeps [.rdx] s t := by
  crun
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

private theorem saveMask_ok (s : State) (dst src : Reg) :
    WP isa (.block [.mov dst (.reg src)]) s fun t =>
      t.gpr dst = s.gpr src ∧ Keeps [dst] s t := by
  crun [RegUpd.gpr_setReg_self]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem projectiveMatch_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86_64.Cfg.projectiveMatch c)) s fun t =>
      t.gpr .rdx = mask (sv c base s W = 0 ∨
        (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) ∧
      Keeps [.rax,.rdx,.rbp,.r12] s t := by
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.projectiveMatch]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs hc.n0 (sl_le c hc.n10 (i := W) (by decide))) fun s₁ ⟨w₁,k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveMask_ok s₁ .rbp .rdx) fun s₂ ⟨w₂,k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ltN_ok c hs₂ hc.n0 (sl_le c hc.n10 (i := K) (by decide))
    (sl_le c hc.n10 (i := MN) (by decide))) fun s₃ ⟨lt₃,k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveMask_ok s₃ .r12 .rax) fun s₄ ⟨lt₄,k₄⟩ => ?_
  have hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs₄ hc.n0 (sl_le c hc.n10 (i := XN) (by decide))) fun s₅ ⟨xn₅,k₅⟩ => ?_
  refine WP.mono (projectiveMerge_ok s₅) fun t ⟨m₆,k₆⟩ => ?_
  refine ⟨?_, (((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))).trans
    (k₆.mono (by decide))⟩
  rw [m₆, xn₅, k₅.1 .r12 (by decide), lt₄, lt₃,
    k₅.1 .rbp (by decide), k₄.1 .rbp (by decide), k₃.1 .rbp (by decide), w₂, w₁,
    k₄.2.1,k₃.2.1,k₂.2.1,k₁.2.1]
  change (mask (sv c base s XN = 0) &&& mask (sv c base s K < sv c base s MN)) |||
    mask (sv c base s W = 0) = _
  by_cases h1 : sv c base s XN = 0 <;> by_cases h2 : sv c base s K < sv c base s MN <;>
    by_cases h3 : sv c base s W = 0 <;> simp [mask,h1,h2,h3]

/-- Combine the projective comparisons with the input checks and reject infinity. -/
theorem projectiveChecks_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    {g : Reg → BitVec 64} (saved : Spill.Saved s.mem base g VG.Impl.Ecdsa.X86_64.Cfg.saved)
    (A : Prop) [Decidable A] (flag : word s.mem base (c.sl FLAG) = mask A) :
    WP isa (.block (Impl.Ecdsa.Verify.X86_64.Cfg.projectiveChecks c)) s fun t =>
      (∀ r ∈ VG.Impl.Ecdsa.X86_64.Cfg.saved.map Prod.fst, t.gpr r = g r) ∧
      (t.gpr .rax).setWidth 32 = if A ∧ sv c base s RZ ≠ 0 ∧
        (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0)) then 1 else 0 := by
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c hc.n10 (i := FLAG) (by decide); have := hc.n0; omega
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.projectiveChecks]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (projectiveMatch_ok hc hs) fun s₁ ⟨m₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (andFlag_ok' c hs₁ hf) fun s₂ ⟨f₂,k₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₂ hc.n0 (sl_le c hc.n10 (i := RZ) (by decide)) hf)
    fun s₃ ⟨f₃,k₃,O₃⟩ => ?_
  have U : Unch base [(c.sl FLAG,8)] s.mem s₃.mem := by
    rw [← k₁.2.1]; exact (O₂.unch.trans O₃.unch).mono (by simp)
  have saved₃ := Saved.unch saved (fun w hw => by rw [List.mem_singleton.mp hw]; simp (disch := sl_ne) only [sl_eq]; omega) U
  have hz : sv c base s₂ RZ = sv c base s RZ := by
    rw [sv, O₂.wordsVal (by have := sl_apart c (i := RZ) (j := FLAG) (by decide); have := hc.n0; omega)
      (by have := sl_le c hc.n10 (i := RZ) (by decide); have := hs.nowrap; omega), k₁.2.1]
  have f : word s₃.mem base (c.sl FLAG) = mask (A ∧ sv c base s RZ ≠ 0 ∧
      (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))) := by
    change wordsVal s₂.mem base (c.sl RZ) c.n = sv c base s RZ at hz
    rw [f₃, f₂, k₁.2.1, flag, m₁, hz, mask_and, mask_and]
    congr 1
    exact propext (by grind)
  refine WP.mono (vfinish_ok hc (hs₂.of_keepRegs k₃ (by decide)) saved₃
    (decide (A ∧ sv c base s RZ ≠ 0 ∧
      (sv c base s W = 0 ∨ (sv c base s K < sv c base s MN ∧ sv c base s XN = 0))))
    (by simpa only [mask, decide_eq_true_eq] using f)) fun t ⟨ret,keep⟩ =>
    ⟨keep, by simpa only [decide_eq_true_eq] using ret⟩

end VG.Proof.Ecdsa.Verify.X86_64
