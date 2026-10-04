import VerifiedGarbage.Proof.AesCcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Open

/-!
# AES-CCM on x86-64: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`SealCT.lean`),
with counter mode before the MAC; the comparison, which leaves `ok` at
`W + 224`, and the mask and the exit are checked by the taint analysis from
the public arguments, between which correctness says each run keeps them
(`openCmp_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr cmp)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem openCmp_check : ∃ hc, (taint.check (ccmT [])
    (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (.seq recv (.seq (cmp uO)
      (.block [.store (at_ .r15 okO) .rax])))) hc).isSome = true := ⟨_, by taint_decide⟩

theorem openMask_check : ∃ hc, (taint.check (ccmT [])
    (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The comparison keeps the public arguments. -/
theorem openCmp_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) {s : State} (h : Mid K W SP R N A D nl al n tl s) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (.seq recv (.seq (cmp uO)
      (.block [.store (at_ .r15 okO) .rax])))) s (One K W SP R N A D nl al n tl) := by
  obtain ⟨o, -, -, hD⟩ := h
  refine WP.mono (openCmp_ok L o.env o.sl (by omega) ht16) fun s₄ ⟨E₄, _, wr₄, f₄, _⟩ => ?_
  refine ⟨E₄, slots_mut L hD.w (f₄.sub fun r hr => ?_) o.sl, wr₄.trans o.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64)
    (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Pre₀ K W SP R N A D nl al n tl s₁ ∧ Pre₀ K W SP R N A D nl al n tl s₂) :
    RelCT isa P (.seq ctrs (.seq (ctr v.callee) (.seq (mac v.callee v.suffix uO) (.seq (tag v.callee uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO))]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 okO) .rax]) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore))))))))))) fun _ _ => True := by
  have hy : uO = 0 ∨ uO = 96 := .inr rfl
  have r₁ := (rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) ctrs_check).wp
    (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl) fun s₁ s₂ h => by
      obtain ⟨⟨o₁, n₁, a₁, d₁⟩, ⟨o₂, n₂, a₂, d₂⟩⟩ := hP _ _ h
      exact ⟨ctrs_mid L o₁ n₁ a₁ d₁ h7 h13, ctrs_mid L o₂ n₂ a₂ d₂ h7 h13⟩
  have r₂ := (rel_of_pt (c := ctr v.callee)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact crypt_rel v C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl)
    fun _ _ h => ⟨ctr_mid v L hR h7 h13 hn' hdk h.2.1, ctr_mid v L hR h7 h13 hn' hdk h.2.2⟩
  have r₃ := (mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' hy
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂)
    fun _ _ h => ⟨h.2.1, h.2.2⟩).wp (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl)
    fun _ _ h => ⟨mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.1, mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.2⟩
  have r₄ := (tag_rel v L hR hDW hn h7 h13 hy
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl) (F₂ := Mid K W SP R N A D nl al n tl)
    fun _ _ h => ⟨tag_mid v L hR h7 h13 hy h.2.1, tag_mid v L hR h7 h13 hy h.2.2⟩
  have r₅ := (rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl s₁ ∧ Mid K W SP R N A D nl al n tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.2.1.1 h.2.2.1 fun _ h => nomatch h) openCmp_check).wp
    (F₁ := One K W SP R N A D nl al n tl) (F₂ := One K W SP R N A D nl al n tl)
    fun _ _ h => ⟨openCmp_one L ht4 ht16 h.2.1, openCmp_one L ht4 ht16 h.2.2⟩
  have r₆ := rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.2.1 h.2.2 fun _ h => nomatch h) openMask_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (rel_assoc4 (RelCT.seq r₅ r₆)))))

/-- `vg_aes_ccm_open`, in two runs with the same public arguments. -/
theorem open_rel (v : Ctr32Impl) {s₀ s₀' : State} (hp : onePre s₀) (hp' : onePre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee v.suffix) fun _ _ => True := by
  have Ar := args_of hp
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in hp) (argW_in hp')
    (entry_pre_self hp) (entry_pre_pub hp' hq)) ?_
  exact openBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.aad.lt Ar.hn Ar.dk fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesCcm.X86_64
