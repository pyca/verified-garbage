module

public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.LaneTaint

/-!
# Clearing registers keeps a function verified (AArch64)

`Verified.withClears`: code verified against a contract that `Sig.contract`
derives (or any whose postcondition reads only the memory and `x0`,
`Verified.withClears_of`) is still verified after a block of clears
(`clearOk`: `movz` of a register that is neither preserved nor `x0`, `movi0`
of a vector register that is not preserved, `mov vd.d[1], xn`, which writes
only the high half of `vd`, which the calling convention does not preserve,
and `tst`), which runs from every state, leaks nothing, and changes neither
the memory, nor `x0`, nor what the calling convention preserves (the
preserved registers, and the low halves of `v8`–`v15`), which is all such a
contract's postcondition and the calling convention look at (`post_congr`).
-/

@[expose] public section

namespace VG.AArch64.Clears

/-- The instructions a block of clears may have (see the module docs). -/
def clearOk : Instr → Bool
  | .movz .x r _ hw => hw == 0 && !preserved.contains r && r != .x0
  | .vop (.movi0 v) => !preservedV.contains v
  | .vop (.ins .d2 _ 1 _) => true
  | .tst .x _ _ => true
  | _ => false

/-- What a clear keeps. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.gpr .x0 = s.gpr .x0 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
    s'.sp = s.sp ∧ ∀ v ∈ preservedV, (s'.v v).extractLsb' 0 64 = (s.v v).extractLsb' 0 64

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
      rw [RegUpd.v_setV_of_ne _ _ fun he => ?_]
      subst he
      exact (by simpa using h : q ∉ preservedV) hq
    case ins a d k n =>
      cases a
      case d2 =>
        cases k with
        | zero => simp only [clearOk, Bool.false_eq_true] at h
        | succ k =>
          cases k with
          | succ => simp only [clearOk, Bool.false_eq_true] at h
          | zero =>
            refine ⟨_, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, fun q _ => ?_⟩
            by_cases he : q = d
            · subst he
              rw [RegUpd.v_setV_self, LaneTaint.extract_setLane _ _ (by decide) (j := 0) (by decide)]
              rfl
            · rw [RegUpd.v_setV_of_ne _ _ he]
      all_goals simp only [clearOk, Bool.false_eq_true] at h
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

/-- A block of clears after correct code keeps it correct, for a
postcondition that looks at the final state only through its memory and
`x0`. -/
theorem correct_withClears {pre : State → Prop} {post : State → State → Prop} {c : Prog isa}
    {cl : List Instr}
    (h : ∀ s, pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ post s s')
    (hpost : ∀ {s u u'}, post s u → u'.mem = u.mem → u'.gpr .x0 = u.gpr .x0 → post s u')
    (hcl : cl.all clearOk = true) :
    ∀ s, pre s → ∃ t s', Exec isa (.seq c (.block cl)) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  intro s hs
  obtain ⟨t, s', he, ⟨hg, hsp, hv⟩, hq⟩ := h s hs
  obtain ⟨s'', hb, hm, hx0, hpr, hsp', hpv⟩ := execBlock_clearOk cl hcl s'
  refine ⟨t ++ [], s'', .seq he (.block hb), ⟨fun r hr => ?_, hsp'.trans hsp, fun r hr => ?_⟩,
    hpost hq hm hx0⟩
  · rw [hpr r hr, hg r hr]
  · rw [hpv r hr, hv r hr]

/-- A block of clears after constant-time code keeps it constant time: it
runs from every state and accesses no memory. -/
theorem ct_withClears {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    {cl : List Instr} (h : ConstantTime isa pre pub c) (hcl : cl.all clearOk = true) :
    ConstantTime isa pre pub (.seq c (.block cl)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      rw [h _ _ _ _ _ _ h₁ h₂ hp a₁ a₂]
      cases b₁ with
      | block hb₁ =>
        cases b₂ with
        | block hb₂ =>
          obtain ⟨_, hc₁, -⟩ := execBlock_clearOk cl hcl _
          obtain ⟨_, hc₂, -⟩ := execBlock_clearOk cl hcl _
          rw [hc₁] at hb₁; rw [hc₂] at hb₂
          cases hb₁; cases hb₂; rfl

/-- Code verified against a contract whose postcondition looks at the final
state only through its memory and `x0` is still verified after a block of
clears. -/
theorem Verified.withClears_of {k : Contract isa} {c : Prog isa} {cl : List Instr}
    (h : Verified target c k)
    (hpost : ∀ {s u u'}, k.post s u → u'.mem = u.mem → u'.gpr .x0 = u.gpr .x0 → k.post s u')
    (hcl : cl.all clearOk = true) : Verified target (.seq c (.block cl)) k :=
  ⟨correct_withClears h.1 hpost hcl, ct_withClears h.2.1 hcl, h.2.2⟩

theorem Verified.withClears {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {c : Prog isa}
    {cl : List Instr} (h : Verified target c (sig.contract abi pre post wa stack leak))
    (hcl : cl.all clearOk = true) :
    Verified target (.seq c (.block cl)) (sig.contract abi pre post wa stack leak) :=
  Verified.withClears_of h (fun hq hm hx => post_congr hq hm hx) hcl

end VG.AArch64.Clears
