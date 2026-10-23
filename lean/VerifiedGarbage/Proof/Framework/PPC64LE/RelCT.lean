module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-!
# Constant time of calls, by relating two runs (PPC64LE)

As on AArch64 (`Proof/Framework/AArch64/RelCT.lean`): a call of verified
code leaks the same trace in two runs when the callee's contract holds in
both (narrowed to the regions it is given, as `WP.call` does) and its public
data agrees, since the callee's run from the narrowed state is the actual
run with fewer permissions (`Exec.widen` and determinism), and the callee is
constant time. `bl` and `blr` leak no addresses of their own. A frame saving a
register (`RelCT.frame`) leaks the addresses of its push and pop, which
depend only on the stack pointer.
-/

@[expose] public section

namespace VG.PPC64LE

/-- The permissions of PPC64LE states, for the inlining theory
(`Proof/Framework/Inline.lean`). -/
def regionModel : RegionModel isa where
  rd := State.rd
  wr := State.wr
  mem := State.mem
  withRegions := State.withRegions
  rd_with _ _ _ := rfl
  wr_with _ _ _ := rfl
  mem_with _ _ _ := rfl
  with_self _ := rfl
  with_with _ _ _ _ _ := rfl
  exec_regions h := ⟨(exec_regions h).1, (exec_regions h).2.1, (exec_regions h).2.2.2⟩
  exec_widen hc hw h := exec_widen hc hw h
  addrs_with := addrs_withRegions
  eval_with := eval_withRegions
  callAddrs_with _ _ _ := rfl
  retAddrs_with _ _ _ := rfl
  call_widen h := by
    simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  ret_widen h := by
    simp only [isa, ret] at h; split at h <;> cases h; rename_i hc
    exact ⟨rfl, rfl, fun _ _ => (ite_eq_left hc).trans rfl⟩
  push_widen h := by
    obtain ⟨f, hr, hw, -⟩ := push_widen h [] []
    refine ⟨f, hr, hw, fun rd wr => ?_⟩
    obtain ⟨f', -, hw', he⟩ := push_widen h rd wr
    rw [hw] at hw'
    rw [← (List.cons.inj hw').1] at he
    exact he
  pop_widen h := ⟨(pop_eq h).1, (pop_eq h).2.1, (pop_eq h).2.2.1, fun _ _ hw => pop_widen h _ hw⟩

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

/-- Two runs of a frame saving a register leak the same trace when the stack
pointer agrees and the runs of its body, from the states after the push, do;
the stack pointer agrees after it too. -/
theorem RelCT.frame {r r' : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed r s₁ ∧ b = pushed r s₂) body R) :
    RelCT isa P (.frame (.push r) body (.pop r')) fun a b => a.sp = b.sp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.push r) s = some a → a = pushed r s := by
    intro s a h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  have hsp' : ∀ {s s₂ s' : State}, isa.pop (.pop r') (pushed r s) s₂ = some s' → s₂.sp = s.sp - 48 ∧
      s'.sp = s.sp := by
    intro s s₂ s' h
    obtain ⟨-, -, -, -, e, n, hn, e'⟩ := pop_eq h
    simp only [pushed, List.head?_cons, Option.some.injEq, Region.mk.injEq] at hn
    rw [e', e, ← hn.2]
    exact ⟨rfl, by simp only [pushed]; bv_omega⟩
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      obtain ⟨g₁, g₁'⟩ := hsp' q₁
      obtain ⟨g₂, g₂'⟩ := hsp' q₂
      have e := hsp _ _ hp
      refine ⟨?_, show s₁'.sp = s₂'.sp by rw [g₁', g₂', e]⟩
      simp only [addrs, g₁, g₂, e]

end VG.PPC64LE
