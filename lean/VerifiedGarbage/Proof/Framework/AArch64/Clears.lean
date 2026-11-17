module

public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# Clearing registers keeps a function verified (AArch64)

`Verified.withClears`: code verified against a contract that `Sig.contract`
derives is still verified after a block of clears (`clearOk`: `movz` of a
register that is neither preserved nor `x0`, `movi0` of a vector register
that is not preserved, `tst`), which runs from every state, leaks nothing,
and changes neither the memory, nor `x0`, nor what the calling convention
preserves, which is all such a contract's postcondition and the calling
convention look at (`post_congr`).
-/

@[expose] public section

namespace VG.AArch64.Clears

/-- The instructions a block of clears may have (see the module docs). -/
def clearOk : Instr → Bool
  | .movz .x r _ hw => hw == 0 && !preserved.contains r && r != .x0
  | .vop (.movi0 v) => !preservedV.contains v
  | .tst .x _ _ => true
  | _ => false

/-- What a clear keeps. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.gpr .x0 = s.gpr .x0 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
    s'.sp = s.sp ∧ ∀ v ∈ preservedV, s'.v v = s.v v

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem Keeps.trans {s t u : State} (h₁ : Keeps s t) (h₂ : Keeps t u) : Keeps s u :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun r hr => (h₂.2.2.1 r hr).trans (h₁.2.2.1 r hr),
    h₂.2.2.2.1.trans h₁.2.2.2.1, fun v hv => (h₂.2.2.2.2 v hv).trans (h₁.2.2.2.2 v hv)⟩

theorem exec_clearOk {i : Instr} (h : clearOk i = true) (s : State) :
    ∃ s', exec i s = some s' ∧ addrs i s = [] ∧ Keeps s s' := by
  cases i
  case movz sz r imm hw =>
    cases sz
    · simp only [clearOk, Bool.false_eq_true] at h
    simp only [clearOk, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    obtain ⟨⟨rfl, hp⟩, hx⟩ := h
    refine ⟨_, rfl, rfl, rfl, ?_, fun q hq => ?_, rfl, fun _ _ => rfl⟩
    · exact RegUpd.gpr_write_of_ne _ _ _ (Ne.symm hx)
    · refine RegUpd.gpr_write_of_ne _ _ _ fun he => ?_
      subst he
      exact (by simpa using hp : q ∉ preserved) hq
  case vop op =>
    cases op
    case movi0 v =>
      simp only [clearOk, Bool.not_eq_true'] at h
      refine ⟨_, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, fun q hq => ?_⟩
      refine RegUpd.v_setV_of_ne _ _ fun he => ?_
      subst he
      exact (by simpa using h : q ∉ preservedV) hq
    all_goals simp only [clearOk, Bool.false_eq_true] at h
  case tst sz n m =>
    cases sz
    · simp only [clearOk, Bool.false_eq_true] at h
    exact ⟨_, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  all_goals simp only [clearOk, Bool.false_eq_true] at h

theorem execBlock_clearOk : ∀ (is : List Instr), is.all clearOk = true → ∀ s,
    ∃ s', execBlock isa is s = some (s', []) ∧ Keeps s s'
  | [], _, s => ⟨s, rfl, Keeps.refl s⟩
  | i :: is, h, s => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨t, ht, ha, hk⟩ := exec_clearOk h.1 s
    obtain ⟨u, hu, hk'⟩ := execBlock_clearOk is h.2 t
    refine ⟨u, ?_, hk.trans hk'⟩
    simp only [execBlock]
    erw [ht]
    simp only [hu, Option.map_some]
    erw [ha]
    rfl

/-- The postcondition of a contract that `Sig.contract` derives looks at the
final state only through its memory and `x0`. -/
theorem post_congr {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s u u' : State}
    (h : (sig.contract abi pre post wa stack leak).post s u) (hm : u'.mem = u.mem)
    (hx : u'.gpr .x0 = u.gpr .x0) : (sig.contract abi pre post wa stack leak).post s u' := by
  have hm' : abi.mem u' = abi.mem u := hm
  have hx' : abi.ret u' = abi.ret u := hx
  revert h
  simp only [Sig.contract]
  split
  · exact id
  · rw [hm', hx']; exact id

theorem Verified.withClears {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa}
    {cl : List Instr} (h : Verified target c (sig.contract abi pre post wa stack leak))
    (hcl : cl.all clearOk = true) :
    Verified target (.seq c (.block cl)) (sig.contract abi pre post wa stack leak) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, ⟨hg, hsp, hv⟩, hq⟩ := hcor s hs
    obtain ⟨s'', hb, hm, hx0, hpr, hsp', hpv⟩ := execBlock_clearOk cl hcl s'
    refine ⟨t ++ [], s'', .seq he (.block hb), ⟨fun r hr => ?_, hsp'.trans hsp, fun r hr => ?_⟩,
      post_congr hq hm hx0⟩
    · rw [hpr r hr, hg r hr]
    · rw [hpv r hr, hv r hr]
  · cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq a₂ b₂ =>
        rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂]
        cases b₁ with
        | block hb₁ =>
          cases b₂ with
          | block hb₂ =>
            obtain ⟨_, hc₁, -⟩ := execBlock_clearOk cl hcl _
            obtain ⟨_, hc₂, -⟩ := execBlock_clearOk cl hcl _
            rw [hc₁] at hb₁; rw [hc₂] at hb₂
            cases hb₁; cases hb₂; rfl

end VG.AArch64.Clears
