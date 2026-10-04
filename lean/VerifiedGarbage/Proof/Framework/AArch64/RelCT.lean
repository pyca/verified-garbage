import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Constant time of calls, by relating two runs (AArch64)

As on x86-64 (`Proof/Framework/X86_64/RelCT.lean`): a call of verified code
leaks the same trace in two runs when the callee's contract holds in both
(narrowed to the regions it is given, as `WP.call` does) and its public data
agrees, since the callee's run from the narrowed state is the actual run
with fewer permissions (`Exec.widen` and determinism), and the callee is
constant time. `bl` and `ret` leak no addresses of their own.
-/

namespace VG.AArch64

/-- The trace of a run of verified code, with more permissions than its
contract gives it, is that of the run its contract describes. -/
theorem trace_narrow {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {t : List Leak} {s' : State}
    (he : Exec isa c s t s') :
    ∃ s'', Exec isa c (s.withRegions rd wr) t s'' :=
  regionModel.trace_narrow hv hpre hc hw he

theorem RelCT.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine regionModel.relCT_call hv hct fun s₁ s₂ e₁ e₂ hp h₁ h₂ => ?_
  rw [call_callEntry, Option.some.injEq] at h₁ h₂
  subst h₁ h₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  exact ⟨rd, wr, rd, wr, p₁, p₂, hpub, c₁, w₁, c₂, w₂, rfl, fun _ _ _ _ _ _ => rfl⟩

/-- A call of verified code, narrowed in each run to regions of its own. -/
theorem RelCT.callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine regionModel.relCT_call hv hct fun s₁ s₂ e₁ e₂ hp h₁ h₂ => ?_
  rw [call_callEntry, Option.some.injEq] at h₁ h₂
  subst h₁ h₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  exact ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, rfl, fun _ _ _ _ _ _ => rfl⟩

/-- A frame saving a register leaks only `sp`. -/
theorem RelCT.pushFrame {r r' : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t) body R) :
    RelCT isa P (.frame (.push r) body (.pop r')) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have push_eq : ∀ {a b : State}, isa.push (.push r) a = some b → b = pushed r a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := push_eq ps
      have eb := push_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      have sp₁ := (Exec.rdwr bs).2.2
      have sp₂ := (Exec.rdwr bt).2.2
      have he := hsp s t hp
      refine ⟨?_, trivial⟩
      simp only [addrs, sp₁, sp₂, pushed, he]

/-- Allocating and freeing a buffer leaks nothing. -/
theorem RelCT.alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
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

end VG.AArch64
