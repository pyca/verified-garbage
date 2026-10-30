module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

-- separate module: `CT.lean` evaluates this analysis with `taint_decide`, so it imports it with
-- `meta import`, which needs a module of its own.

/-!
# X25519 on 32-bit ARM: a taint analysis for `umaal`

The ARMv7 analysis (`taint`) does not analyse `umaal`, which writes two
registers. This one does, as making both of them secret, and leaves every
other instruction to `taint`: `vg_x25519_umaal`'s multiplications use the
values `umaal` writes only as data, never in an address or a branch.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.UmaalTaint

open VG VG.Arm

/-- `τ` after writing secret values to `lo` and `hi`. -/
def secret2 (τ : VG.Arm.Taint.T) (lo hi : Reg) : VG.Arm.Taint.T where
  regs := (τ.regs.erase lo).erase hi
  flags := τ.flags
  lens := τ.lens
  bases := τ.bases.filter fun p => !VG.Arm.Taint.regEq p.1 lo && !VG.Arm.Taint.regEq p.1 hi
  slots := τ.slots
  argLen := τ.argLen
  argBases := τ.argBases

/-- `taint`'s step, and `umaal lo hi n m` making `lo` and `hi` secret. -/
def step (τ : VG.Arm.Taint.T) (i : Instr) : Option VG.Arm.Taint.T :=
  match i with
  | .umaal lo hi _ _ => some (secret2 τ lo hi)
  | _ => taint.step τ i

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

theorem umaal_sound {τ τ' : VG.Arm.Taint.T} {lo hi n m : Reg} {s₁ s₂ s₁' s₂' : State}
    (ha : VG.Arm.Taint.Agree τ s₁ s₂) (hs : step τ (.umaal lo hi n m) = some τ')
    (e₁ : exec (.umaal lo hi n m) s₁ = some s₁') (e₂ : exec (.umaal lo hi n m) s₂ = some s₂') :
    addrs (.umaal lo hi n m) s₁ = addrs (.umaal lo hi n m) s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  obtain rfl : secret2 τ lo hi = τ' := Option.some.inj hs
  obtain ⟨w₁, m₁, sp₁, n₁, z₁, c₁, v₁, g₁⟩ := umaal_exec e₁
  obtain ⟨w₂, m₂, sp₂, n₂, z₂, c₂, v₂, g₂⟩ := umaal_exec e₂
  have hb : ∀ {s s' : State}, VG.Arm.Taint.Wf τ s → s'.wr = s.wr →
      (∀ r, r ≠ lo → r ≠ hi → s'.gpr r = s.gpr r) →
      ∀ p ∈ (secret2 τ lo hi).bases, State.addr (s'.gpr p.1) = (VG.Arm.Taint.region s' p.2).base := by
    intro s s' hw hwr hg p hp
    simp only [secret2, List.mem_filter, VG.Arm.Taint.regEq_eq, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at hp
    rw [hg _ hp.2.1 hp.2.2, hw.bases p hp.1]
    simp [VG.Arm.Taint.region, hwr]
  refine ⟨rfl, ha.keep ⟨fun r hr => ?_, fun hf => ?_⟩ rfl rfl rfl rfl w₁ w₂ m₁ m₂ sp₁ sp₂
    (hb ha.wf₁ w₁ g₁) (hb ha.wf₂ w₂ g₂)⟩
  · change r ∈ (τ.regs.erase lo).erase hi at hr
    simp only [RegSet.mem_erase] at hr
    rw [g₁ r hr.2.1 hr.1, g₂ r hr.2.1 hr.1]
    exact ha.rf.1 r hr.2.2
  · rw [n₁, z₁, c₁, v₁, n₂, z₂, c₂, v₂]; exact ha.rf.2 hf

private theorem base_sound {τ τ' : VG.Arm.Taint.T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : VG.Arm.Taint.Agree τ s₁ s₂) (hs : VG.Arm.Taint.stepKM τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' :=
  taint.step_sound ha hs e₁ e₂

theorem sound {τ τ' : VG.Arm.Taint.T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : VG.Arm.Taint.Agree τ s₁ s₂) (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  cases i with
  | umaal => exact umaal_sound ha hs e₁ e₂
  | _ => exact base_sound ha hs e₁ e₂

/-- `taint`, with `step` for its step. -/
def analysis : VG.Taint isa := { taint with step := step, step_sound := sound }

end VG.Proof.X25519.Arm.UmaalTaint
