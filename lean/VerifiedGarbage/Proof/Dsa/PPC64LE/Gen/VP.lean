module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-! # DSA parameter generation on PPC64LE: pieces proven correct and constant time at once

As on ARMv7 (`Proof/Rsa/Arm/RvVP.lean`): `VP F c G`: from any state at the
stage `F σ` of a run from `σ`, `c` ends at the stage `G σ` (`wp`), and two
runs, each at the stage `F` of its own run, leak the same trace and end at
the stages `G` (`ct`). The stages carry the public parameters both runs
share, so that a piece checked by the taint analysis needs only that the
registers it takes as public are determined by them (`VP.taint`), and pieces
compose by `seq`, `ite` and `loop` (whose number of iterations is public).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE

/-- Two runs, each at the stage `F` of its own run from `σ`. -/
def Two (F : State → State → Prop) (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, F σ₁ s₁ ∧ F σ₂ s₂

/-- The stage `F` of a run from `σ`, whose states name the statics `σ` names. -/
def Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

structure VP (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop where
  wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)
  ct : RelCT isa (Two (Sy F)) c (Two (Sy G))

namespace VP

variable {F G H : State → State → Prop}

/-- The stage after a piece names the statics of the run's start. -/
theorem wps {c : Prog isa} (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) {σ s : State}
    (hs : F σ s) (hy : s.syms = σ.syms) : WP isa c s (Sy G σ) :=
  WP.mono_syms (wp σ s hs hy) fun _ ht ty => ⟨ht, ty.trans hy⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct' {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => Sy F σ₁ s₁ ∧ Sy F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) : VP F c G := by
  refine ⟨wp, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂
  have r := ((ct σ₁ σ₂).wp (F₁ := Sy G σ₁) (F₂ := Sy G σ₂) fun s t h =>
    ⟨wps wp h.1.1 h.1.2, wps wp h.2.1 h.2.2⟩) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, r.2.2.1, r.2.2.2⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => F σ₁ s₁ ∧ F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  of_ct' (fun σ₁ σ₂ => (ct σ₁ σ₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    fun σ s hs _ => wp σ s hs

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem taint {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs rs) c hc).isSome = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hc) wp

theorem mono {F' G' : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hF : ∀ σ s, F' σ s → F σ s) (hG : ∀ σ s, G σ s → G' σ s) : VP F' c G' :=
  ⟨fun σ s hs hy => WP.mono (h.wp σ s (hF σ s hs) hy) (hG σ),
    h.ct.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hF _ _ h₁.1, h₁.2⟩, ⟨hF _ _ h₂.1, h₂.2⟩⟩)
      fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hG _ _ h₁.1, h₁.2⟩, ⟨hG _ _ h₂.1, h₂.2⟩⟩⟩

theorem seq {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VP G c₂ H) : VP F (.seq c₁ c₂) H :=
  ⟨fun σ _ hs hy => WP.seq (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2), RelCT.seq h₁.ct h₂.ct⟩

theorem assoc {a b c : Prog isa} (h : VP F (.seq (.seq a b) c) G) : VP F (.seq a (.seq b c)) G :=
  ⟨fun σ s hs hy => WP.assoc (h.wp σ s hs hy), RelCT.assoc h.ct⟩

theorem block_append {l₁ l₂ : List Instr} (h₁ : VP F (.block l₁) G) (h₂ : VP G (.block l₂) H) :
    VP F (.block (l₁ ++ l₂)) H :=
  ⟨fun σ _ hs hy => WP.block_append (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2),
    RelCT.block_append (RelCT.seq h₁.ct h₂.ct)⟩

theorem block_nil (h : ∀ σ s, F σ s → G σ s) : VP F (.block []) G :=
  ⟨fun σ s hs _ => WP.block_nil (h σ s hs),
    RelCT.block_nil fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨h _ _ h₁.1, h₁.2⟩, ⟨h _ _ h₂.1, h₂.2⟩⟩⟩

/-- A branch on a condition both runs agree on. -/
theorem ite {c : Cond} {t e : Prog isa}
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VP (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VP (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VP F (.ite c t e) G := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, isa.eval c s = some b := by cases c <;> exact ⟨_, rfl⟩
    exact WP.ite b hb (fun h => ht.wp σ s ⟨hs, by rw [hb, h]⟩ hy) (fun h => he.wp σ s ⟨hs, by rw [hb, h]⟩ hy)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁.1 h₂.1) ?_ ?_
    · exact ht.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h
    · exact he.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h

/-- A loop whose iterations left, `n + 1` at the stage `I (n + 1)`, both
runs share: each iteration goes on iff `n > 0`. -/
theorem loop {I : Nat → State → State → Prop} {body : Prog isa} {c : Cond} {Q : State → State → Prop}
    (hb : ∀ n, VP (I (n + 1)) body fun σ s =>
      isa.eval c s = some (decide (0 < n)) ∧ (n = 0 → Q σ s) ∧ (0 < n → I n σ s))
    (n : Nat) : VP (I (n + 1)) (.loop body c) Q := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · refine WP.loop (M := isa) (Q := Q σ) (fun m u => Sy (I (m + 1)) σ u) (fun m u hu => ?_) n s ⟨hs, hy⟩
    refine WP.mono (wps (hb m).wp hu.1 hu.2) fun u' ⟨⟨he, hq, hi⟩, uy⟩ => ?_
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · exact .inl ⟨by rw [he, h0]; rfl, hq h0⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .inr ⟨by rw [he]; simp, k, by omega, hi hp, uy⟩
  · refine RelCT.loop (M := isa) (fun m => Two (Sy (I (m + 1)))) (fun m => ?_) n
    refine (hb m).ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨σ₁, σ₂, ⟨⟨e₁, q₁, i₁⟩, y₁⟩, ⟨⟨e₂, q₂, i₂⟩, y₂⟩⟩ =>
      ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ?_⟩
    · have h0 : m = 0 := by rw [e₁] at hf; simpa using hf
      exact ⟨σ₁, σ₂, ⟨q₁ h0, y₁⟩, ⟨q₂ h0, y₂⟩⟩
    · have hp : 0 < m := by rw [e₁] at ht; simpa using ht
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact ⟨k, by omega, σ₁, σ₂, ⟨i₁ hp, y₁⟩, ⟨i₂ hp, y₂⟩⟩

/-- A piece no state reaches. -/
theorem of_false {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁.1 (h σ _)⟩

end VP

end VG.Proof.Dsa.PPC64LE.Gen
