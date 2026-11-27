module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.ModeSim

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

/-- Code that leaves the same MXCSR in two runs along the same trace from the
same (`MxDet`): two runs of it related by `P`, from the same MXCSR, end with
the same MXCSR too. -/
theorem RelCT.and_mx {c : Prog isa} {P Q : State → State → Prop} (hmx : MxDet c)
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.mxcsr = s₂.mxcsr) (h : RelCT isa P c Q) :
    RelCT isa P c fun a b => Q a b ∧ a.mxcsr = b.mxcsr := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  exact ⟨ht, hq, hmx _ _ _ _ _ e₁ (ht ▸ e₂) (hP _ _ hp)⟩

/-- A call whose callee leaves the same MXCSR in two runs along the same trace
from the same MXCSR (`MxDet`): two runs of it related by `P`, from the same
MXCSR, return with the same MXCSR too. -/
theorem RelCT.call_mx {n : String} {c : Prog isa} {P Q : State → State → Prop} (hmx : MxDet c)
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.mxcsr = s₂.mxcsr) (h : RelCT isa P (.call n c) Q) :
    RelCT isa P (.call n c) fun a b => Q a b ∧ a.mxcsr = b.mxcsr := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  refine ⟨ht, hq, ?_⟩
  cases e₁ with
  | call c₁ b₁ r₁ =>
    cases e₂ with
    | call c₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at c₁ c₂
      subst c₁ c₂
      simp only [isa, ret] at r₁ r₂
      split at r₁ <;> cases r₁
      split at r₂ <;> cases r₂
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq] at ht
      obtain ⟨-, ht⟩ := ht
      have ht' := List.append_inj_left' ht rfl
      have hm : s₁.callEntry.mxcsr = s₂.callEntry.mxcsr := hP s₁ s₂ hp
      have hb₂ := ht' ▸ b₂
      have hfin := hmx _ _ _ _ _ b₁ hb₂ hm
      exact hfin

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

/-- Code the taint analysis proves constant time, which leaves the registers
`rs` public: they agree in the final states. -/
theorem RelCT.taintRegs {τ : Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → Taint.Agree τ s₁ s₂) (rs : List Reg) {hc : VG.Taint.Hint Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs) = some true) :
    RelCT isa P c fun s₁ s₂ => ∀ r ∈ rs, s₁.gpr r = s₂.gpr r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

/-- `RelCT.callEx` for a callee that never touches the mode: the second run's
entry is related to the first's with the first's mode (`Contract.mxFree`). -/
theorem RelCT.callExMx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hnt : c.allInstrs (fun i => !touchesMxcsr i) = true)
    (hpre : ∀ s m, k.pre s → k.pre (s.withMx m)) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁)
        ((s₂.callEntry.withRegions rd₂ wr₂).withMx (s₁.callEntry.withRegions rd₁ wr₁).mxcsr) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call n c) fun _ _ => True :=
  RelCT.callEx (k := k.mxFree) hv (Contract.ct_mxFree hnt hct hpre) hP

end VG.X86_64
