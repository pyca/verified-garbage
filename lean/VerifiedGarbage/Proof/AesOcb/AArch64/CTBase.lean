import VerifiedGarbage.Proof.AesOcb.AArch64.Args
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# AES-OCB on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (AES-GCM's `Eq2`) piece by piece, as
AES-GCM's do (`Proof/AesGcm/AArch64/Rel.lean`): the code between calls by
the taint analysis, from the registers `Env` fixes and others the
correctness proofs pin to the same values in both runs (`rel_env`); each call
of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` with the same arguments
in both runs (`callBlocks_rel`); and the next piece from the states the
correctness proofs describe (`rel_seq`). The taint analysis takes memory as
secret, so a block that loads a public value (an argument kept in `W`) and
uses it as an address or a count is split after the load.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint)

/-- Code the taint analysis checks, from the registers `rs` the two runs
agree on and those `Env` fixes. -/
theorem rel_env {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} {c : Prog isa}
    (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (rs ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg))) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  rel_taint _ (by rw [E₁.sp, E₂.sp]) (fun r hr' => by
    rcases List.mem_append.mp hr' with h | h
    · exact hr r h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · rw [E₁.x19, E₂.x19]
      · rw [E₁.x20, E₂.x20]
      · rw [E₁.x21, E₂.x21]
      · rw [E₁.x22, E₂.x22]
      · rw [E₁.x28, E₂.x28]) hc

/-- A call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on the same
`k` blocks at `D'` in both runs. -/
theorem callBlocks_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) (hR : R = 10 ∨ R = 12 ∨ R = 14) {σ₁ σ₂ : State}
    (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) {args : List Instr} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (taint.check (Taint.ofRegs (rs ++ ([.x19, .x20, .x21, .x22, .x28] : List Reg)))
      (.block (args ++ ([Impl.AesGcm.AArch64.mov .x0 .x20, Impl.AesGcm.AArch64.mov .x1 .x22,
        Impl.AesGcm.AArch64.ptr .x4 .x19 scrO] : List Instr))) h).isSome = true)
    {D' : Addr} {k : Nat} (a₁ : ArgsOk args σ₁ D' k) (a₂ : ArgsOk args σ₂ D' k) (d₁ : Dst K W σ₁ D' k)
    (d₂ : Dst K W σ₂ D' k) : RelCT isa (Eq2 σ₁ σ₂) (callBlocks b args) TT := by
  unfold callBlocks
  exact rel_seq (rel_env E₁ E₂ rs hr hc) (callArgs_ok L E₁ hR a₁ d₁) (callArgs_ok L E₂ hR a₂ d₂)
    fun τ₁ τ₂ h₁ h₂ => blk_rel ok ct fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨K, D', _, R, k, h₁.1, h₂.1, by rw [h₁.2.2.1, h₂.2.2.1, E₁.sp, E₂.sp]⟩

/-- Two runs from states related by `P`, from each pair. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- Then: the next piece, from what holds of every run of the first (not
only of one, as `rel_seq` takes it). -/
theorem rel_seqE {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (hF₁ : ∀ t s', Exec isa c₁ σ₁ t s' → F₁ s')
    (hF₂ : ∀ t s', Exec isa c₁ σ₂ t s' → F₂ s')
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) : RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => ?_) (rel_of_pt fun τ₁ τ₂ h =>
    h₂ τ₁ τ₂ h.1 h.2)
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨(h₁ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hF₁ _ _ e₁, hF₂ _ _ e₂⟩

/-- Code without calls that writes none of the registers `rs` keeps them, the
stack pointer and the permissions. -/
theorem exec_keep {c : Prog isa} (rs : List Reg) (hk : c.allInstrs (keeps (RegSet.ofList rs)) = true)
    (hn : c.noCalls = true) {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    (∀ r ∈ rs, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk' := instrs_keeps hk
  refine ⟨fun r hr => Exec.gpr (fun i hi => ?_) h (.inl hn), (Exec.rdwr h).2.2, (Exec.rdwr h).1, (Exec.rdwr h).2.1⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hk' i hi) r hr
  simpa using this

/-- An environment, after code without calls that writes none of its registers. -/
theorem Env.exec {K W D : Addr} {R n : Nat} {SP : Addr} {s s' : State} {c : Prog isa} {t : List Leak}
    (E : Env K W D R n SP s) (h : Exec isa c s t s')
    (hk : c.allInstrs (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28])) = true) (hn : c.noCalls = true) :
    Env K W D R n SP s' :=
  let ⟨g, sp, rd, wr⟩ := exec_keep _ hk hn h
  E.keep g sp rd wr

/-- Then: the next piece, in the environment, after code without calls
that keeps it. -/
theorem rel_seqEnv {K W D : Addr} {R n : Nat} {SP : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : Env K W D R n SP σ₁) (E₂ : Env K W D R n SP σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT)
    (hk : c₁.allInstrs (keeps (RegSet.ofList [.x19, .x20, .x21, .x22, .x28])) = true) (hn : c₁.noCalls = true)
    (h₂ : ∀ τ₁ τ₂, Env K W D R n SP τ₁ → Env K W D R n SP τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  rel_seqE h₁ (fun _ _ h => E₁.exec h hk hn) (fun _ _ h => E₂.exec h hk hn) h₂

/-- Two runs of `a; (b; (c; d))` are two runs of `a; ((b; c); d)`. -/
theorem RelCT.assoc_in {a b c d : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq (.seq b c) d)) Q) : RelCT isa P (.seq a (.seq b (.seq c d))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ r₁ =>
    cases r₁ with
    | seq b₁ r₁ =>
      cases r₁ with
      | seq c₁ d₁ =>
        cases e₂ with
        | seq a₂ r₂ =>
          cases r₂ with
          | seq b₂ r₂ =>
            cases r₂ with
            | seq c₂ d₂ =>
              obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq (.seq b₁ c₁) d₁)) (.seq a₂ (.seq (.seq b₂ c₂) d₂))
              simp only [List.append_assoc] at ht
              exact ⟨ht, hq⟩

/-- A register `Env` fixes is not one outside them. -/
theorem envRegs_ne {r : Reg} (hr : r ∈ envRegs) {x : Reg} (hx : x ∉ envRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

end VG.Proof.AesOcb.AArch64
