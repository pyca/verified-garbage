module

public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Syms

/-!
# ARMv7 taint tracking with `umaal`

`taint` and `taintSym L` do not analyse `umaal`, which writes two registers.
`taintU` and `taintSymU L` are them with `umaal lo hi n m` making `lo` and
`hi` secret (`secret2`), whatever its operands: code whose `umaal` results
are only data, never in an address or a branch (the multiplications of
`Impl/Mont/ArmPacked.lean`'s `rowU`), is constant time by them.
-/

@[expose] public section

namespace VG.Arm

namespace Taint

/-- `τ` after secret values are written to `lo` and `hi`. -/
def secret2 (τ : T) (lo hi : Reg) : T where
  regs := (τ.regs.erase lo).erase hi
  flags := τ.flags
  lens := τ.lens
  bases := τ.bases.filter fun p => !regEq p.1 lo && !regEq p.1 hi
  slots := τ.slots
  argLen := τ.argLen
  argBases := τ.argBases

/-- `umaal lo hi n m` changes only `lo` and `hi`. -/
theorem umaal_exec {s s' : State} {lo hi n m : Reg} (h : exec (.umaal lo hi n m) s = some s') :
    s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.n = s.n ∧ s'.z = s.z ∧ s'.c = s.c ∧ s'.v = s.v ∧
      ∀ r, r ≠ lo → r ≠ hi → s'.gpr r = s.gpr r := by
  by_cases same : lo = hi
  · simp only [exec, same, ite_true, reduceCtorEq] at h
  · simp only [exec, same, ite_false, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r h1 h2 => by
      rw [RegUpd.gpr_setReg_of_ne _ _ h2, RegUpd.gpr_setReg_of_ne _ _ h1]⟩

theorem Agree.umaal {τ : T} {lo hi n m : Reg} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (e₁ : exec (.umaal lo hi n m) s₁ = some s₁') (e₂ : exec (.umaal lo hi n m) s₂ = some s₂') :
    Agree (secret2 τ lo hi) s₁' s₂' := by
  obtain ⟨w₁, m₁, sp₁, n₁, z₁, c₁, v₁, g₁⟩ := umaal_exec e₁
  obtain ⟨w₂, m₂, sp₂, n₂, z₂, c₂, v₂, g₂⟩ := umaal_exec e₂
  have hb : ∀ {s s' : State}, Wf τ s → s'.wr = s.wr → (∀ r, r ≠ lo → r ≠ hi → s'.gpr r = s.gpr r) →
      ∀ p ∈ (secret2 τ lo hi).bases, State.addr (s'.gpr p.1) = (region s' p.2).base := by
    intro s s' hw hwr hg p hp
    simp only [secret2, List.mem_filter, regEq_eq, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at hp
    rw [hg _ hp.2.1 hp.2.2, hw.bases p hp.1]
    simp [region, hwr]
  refine ha.keep ⟨fun r hr => ?_, fun hf => ?_⟩ rfl rfl rfl rfl w₁ w₂ m₁ m₂ sp₁ sp₂
    (hb ha.wf₁ w₁ g₁) (hb ha.wf₂ w₂ g₂)
  · change r ∈ (τ.regs.erase lo).erase hi at hr
    simp only [RegSet.mem_erase] at hr
    rw [g₁ r hr.2.1 hr.1, g₂ r hr.2.1 hr.1]
    exact ha.rf.1 r hr.2.2
  · rw [n₁, z₁, c₁, v₁, n₂, z₂, c₂, v₂]; exact ha.rf.2 hf

/-- `taint`'s step, and `umaal` making the registers it writes secret. -/
def stepU (τ : T) (i : Instr) : Option T :=
  match i with
  | .umaal lo hi _ _ => some (secret2 τ lo hi)
  | _ => stepKM τ i

/-- `taintSym L`'s step, and `umaal` making the registers it writes secret. -/
def stepSU (L : List String) (τ : T) (i : Instr) : Option T :=
  match i with
  | .umaal lo hi _ _ => some (secret2 τ lo hi)
  | _ => stepS L τ i

private theorem base_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : stepKM τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' :=
  taint.step_sound ha hs e₁ e₂

theorem stepU_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : stepU τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | umaal lo hi n m =>
    obtain rfl : secret2 τ lo hi = τ' := Option.some.inj hs
    exact ⟨rfl, ha.umaal e₁ e₂⟩
  | _ => exact base_sound ha hs e₁ e₂

private theorem baseS_sound {L : List String} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeS L τ s₁ s₂) (hs : stepS L τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ AgreeS L τ' s₁' s₂' :=
  stepS_sound ha hs e₁ e₂

theorem stepSU_sound {L : List String} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeS L τ s₁ s₂) (hs : stepSU L τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ AgreeS L τ' s₁' s₂' := by
  cases i with
  | umaal lo hi n m =>
    obtain rfl : secret2 τ lo hi = τ' := Option.some.inj hs
    refine ⟨rfl, ha.1.umaal e₁ e₂, fun nm hn => ?_⟩
    rw [exec_syms e₁, exec_syms e₂]; exact ha.2 nm hn
  | _ => exact baseS_sound ha hs e₁ e₂

end Taint

/-- `taint`, with `umaal` making the registers it writes secret. -/
def taintU : VG.Taint isa := { taint with step := Taint.stepU, step_sound := Taint.stepU_sound }

/-- `taintSym L`, with `umaal` making the registers it writes secret. -/
def taintSymU (L : List String) : VG.Taint isa :=
  { taintSym L with step := Taint.stepSU L, step_sound := Taint.stepSU_sound }

end VG.Arm
