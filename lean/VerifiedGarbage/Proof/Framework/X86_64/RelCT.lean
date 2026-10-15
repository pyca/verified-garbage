module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Constant time of calls, by relating two runs (x86-64)

A call of verified code leaks the same trace in two runs when the callee's
contract holds in both (narrowed to the regions it is given, as `WP.call`
does) and its public data agrees: the callee's run from the narrowed state
is the actual run with fewer permissions (`Exec.widen` and determinism),
and the callee is constant time. The call and return addresses agree when
`rsp` does.
-/

@[expose] public section

namespace VG.X86_64

theorem ret_rsp {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s₂.gpr .rsp = s₁.gpr .rsp := by
  simp only [isa, ret] at h
  split at h
  · exact ‹_ ∧ _›.1
  · cases h

/-- The trace of a run of verified code, with more permissions than its
contract gives it, is that of the run its contract describes. -/
theorem trace_narrow {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {t : List Leak} {s' : State}
    (he : Exec isa c s t s') :
    ∃ s'', Exec isa c (s.withRegions rd wr) t s'' :=
  regionModel.trace_narrow hv hpre hc hw he

/-- A call of verified code, narrowed in each run to regions of its own. -/
theorem RelCT.callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call n c) fun _ _ => True := by
  refine regionModel.relCT_call hv hct fun s₁ s₂ e₁ e₂ hp h₁ h₂ => ?_
  rw [call_callEntry, Option.some.injEq] at h₁ h₂
  subst h₁ h₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, hsp⟩ := hP _ _ hp
  refine ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, by simp only [hsp],
    fun _ _ _ _ r₁ r₂ => ?_⟩
  have q₁ := ret_rsp r₁
  have q₂ := ret_rsp r₂
  simp only [State.callEntry_rsp] at q₁ q₂
  simp only [q₁, q₂, hsp]

theorem RelCT.call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun s₁ s₂ h => ⟨rd, wr, rd, wr, hP s₁ s₂ h⟩

end VG.X86_64
