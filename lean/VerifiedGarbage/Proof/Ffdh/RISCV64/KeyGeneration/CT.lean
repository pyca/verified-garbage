module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Correct
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-! # Relating two runs of the FFDH controllers (RISC-V)

Two runs related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) through a map
of their points, a branch their points fix, and frames that leak nothing of
their own (`relCT_alloc`, `relCT_pushRa`), for the controllers of
`Proof/Ffdh/RISCV64/Cached/SearchProof/` and
`Proof/Ffdh/RISCV64/Generation/Search/`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.KeyGeneration

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨g a, h _ _ h₁, h _ _ h₂, hsp⟩) fun _ _ h => h


/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩


/-- Allocating and freeing a buffer leaks nothing. -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, VG.RISCV64.push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩


/-- A frame saving `ra` around a body proven with the permissions outside it
(as `WP.frameRegAny` runs it) leaks what the body does there: the body's run
in the frame is that run, with more permissions (`Exec.widen`). -/
theorem relCT_pushRa {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hwp : ∀ a b, P a b → (∃ t s', Exec isa body (framed .ra a) t s') ∧
      (∃ t s', Exec isa body (framed .ra b) t s'))
    (hct : RelCT isa (fun x y => ∃ a b, P a b ∧ x = framed .ra a ∧ y = framed .ra b) body
      fun _ _ => True) :
    RelCT isa P (.frame (.push .ra) body (.pop .ra)) fun a b => a.sp = b.sp := by
  refine RelCT.frame (R := fun _ _ => True) hsp ?_
  have widen : ∀ a, ∀ {t s'}, Exec isa body (framed .ra a) t s' →
      Exec isa body (pushed .ra a) t (s'.withRegions a.rd (⟨a.sp - 16, 16⟩ :: a.wr)) := by
    intro a t s' e
    have := Exec.widen e (rd := a.rd) (wr := ⟨a.sp - 16, 16⟩ :: a.wr)
      (Covers.of_mem fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr))
      (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
    exact this
  rintro x y tx ty x' y' ⟨a, b, hab, rfl, rfl⟩ ex ey
  obtain ⟨⟨ta, sa, ea⟩, ⟨tb, sb, eb⟩⟩ := hwp a b hab
  obtain ⟨rfl, -⟩ := Exec.det ex (widen a ea)
  obtain ⟨rfl, -⟩ := Exec.det ey (widen b eb)
  exact ⟨(hct _ _ _ _ _ _ ⟨a, b, hab, rfl, rfl⟩ ea eb).1, trivial⟩


end VG.Proof.Ffdh.RISCV64.KeyGeneration
