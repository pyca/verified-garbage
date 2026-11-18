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
`Impl/Weierstrass/Arm/Mont.lean`'s `rowU`), is constant time by them.
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
  taint.step_sound ha ((taint_step τ i).trans hs) e₁ e₂

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

/-! ### Steps the kernel finds again

`stepU` and `stepSU L`, as `stepKeepM` and `stepKeep` are `stepKM` and
`stepKD` ("Steps the kernel finds again" in `Arm/Taint.lean`): they give
taints that are evaluated, whose bases are those they were given when
neither register `umaal` writes holds one. -/

/-- `secret2`, giving the bases it was given when neither register holds one. -/
def secret2Keep (τ : T) (lo hi : Reg) : Option T :=
  match τ with
  | ⟨rg, f, l, b, sl, a, ab⟩ =>
    keepBases (noBase b lo && noBase b hi) b (KList.filter (fun p => !regEq p.1 lo && !regEq p.1 hi) b) fun b' =>
      ⟨(rg.erase lo).erase hi, f, l, b', sl, a, ab⟩

theorem secret2Keep_eq (τ : T) (lo hi : Reg) : secret2Keep τ lo hi = some (secret2 τ lo hi) := by
  obtain ⟨rg, f, l, b, sl, a, ab⟩ := τ
  have hb : (noBase b lo && noBase b hi) = true →
      KList.filter (fun p => !regEq p.1 lo && !regEq p.1 hi) b = b := fun h => by
    rw [Bool.and_eq_true, noBase, noBase, KList.all_eq, KList.all_eq, List.all_eq_true, List.all_eq_true] at h
    rw [KList.filter_eq]
    exact List.filter_eq_self.mpr fun p hp => by rw [h.1 p hp, h.2 p hp]; rfl
  exact (keepBases_eq (fun b' => ⟨(rg.erase lo).erase hi, f, l, b', sl, a, ab⟩) hb).trans
    (congrArg (fun b' => some (T.mk ((rg.erase lo).erase hi) f l b' sl a ab)) (KList.filter_eq _ b))

/-- `stepKeepMFn`, and `umaal` making the registers it writes secret. -/
def stepKeepUFn : Instr → Step
  | .umaal lo hi _ _ => ⟨fun τ => secret2Keep τ lo hi⟩
  | i => stepKeepMFn i

/-- `stepKeepFn`, and `umaal` making the registers it writes secret. -/
def stepKeepUDFn : Instr → Step
  | .umaal lo hi _ _ => ⟨fun τ => secret2Keep τ lo hi⟩
  | i => stepKeepFn i

/-- `stepKeepUFn`, with its cases closed (`inline_match%`). -/
def stepKeepUFnK : Instr → Step := inline_match% stepKeepUFn stepKeepMFn stepKeepFn stepKDFn

theorem stepKeepUFnK_eq (i : Instr) : stepKeepUFnK i = stepKeepUFn i := by
  cases i <;> rfl

/-- `stepKeepUDFn`, with its cases closed (`inline_match%`). -/
def stepKeepUDFnK : Instr → Step := inline_match% stepKeepUDFn stepKeepFn stepKDFn

theorem stepKeepUDFnK_eq (i : Instr) : stepKeepUDFnK i = stepKeepUDFn i := by
  cases i <;> rfl

/-- `stepU`, giving a taint that is evaluated, and whose bases and slots are
those it was given when the instruction does not change them. -/
def stepKeepU (τ : T) (i : Instr) : Option T :=
  match (stepKeepUFnK i).run τ with
  | some τ' => forceT τ' some
  | none => none

theorem stepKeepU_eq : stepKeepU = stepU := by
  funext τ i
  have h : (stepKeepUFn i).run τ = stepU τ i := by
    have h := stepKeepMFn_run i τ
    cases i
    case umaal lo hi n m => exact secret2Keep_eq τ lo hi
    all_goals exact h
  unfold stepKeepU
  rw [stepKeepUFnK_eq, h]
  cases stepU τ i with
  | none => rfl
  | some τ' => exact forceT_eq τ' some

/-- `stepKD`, and `umaal` making the registers it writes secret. -/
def stepUD (τ : T) (i : Instr) : Option T :=
  match i with
  | .umaal lo hi _ _ => some (secret2 τ lo hi)
  | _ => stepKD τ i

/-- `stepUD`, giving a taint that is evaluated, and whose bases and slots are
those it was given when the instruction does not change them. -/
def stepKeepUD (τ : T) (i : Instr) : Option T :=
  match (stepKeepUDFnK i).run τ with
  | some τ' => forceT τ' some
  | none => none

theorem stepKeepUD_eq : stepKeepUD = stepUD := by
  funext τ i
  have h : (stepKeepUDFn i).run τ = stepUD τ i := by
    have h := stepKeepFn_run i τ
    cases i
    case umaal lo hi n m => exact secret2Keep_eq τ lo hi
    all_goals exact h
  unfold stepKeepUD
  rw [stepKeepUDFnK_eq, h]
  cases stepUD τ i with
  | none => rfl
  | some τ' => exact forceT_eq τ' some

/-- `stepSU L`, giving a taint that is evaluated, and whose bases and slots
are those it was given when the instruction does not change them. -/
def stepKeepSU (L : List String) (τ : T) (i : Instr) : Option T := stepKeepUD τ (i.symMov L)

theorem stepKeepSU_eq (L : List String) : stepKeepSU L = stepSU L := by
  funext τ i
  unfold stepKeepSU
  rw [stepKeepUD_eq]
  cases i
  case umaal lo hi n m => rfl
  case adrSym d n =>
    show stepUD τ ((Instr.adrSym d n).symMov L) = stepKeep τ ((Instr.adrSym d n).symMov L)
    rw [stepKeep_eq]
    simp only [Instr.symMov]
    split <;> rfl
  all_goals exact (congrFun (congrFun stepKeep_eq τ) _).symm

theorem stepKeepU_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : stepKeepU τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' :=
  stepU_sound ha (stepKeepU_eq ▸ hs) e₁ e₂

theorem stepKeepSU_sound {L : List String} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeS L τ s₁ s₂) (hs : stepKeepSU L τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ AgreeS L τ' s₁' s₂' :=
  stepSU_sound ha (stepKeepSU_eq L ▸ hs) e₁ e₂

end Taint

/-- `taint`, with `umaal` making the registers it writes secret. -/
def taintU : VG.Taint isa := { taint with step := Taint.stepKeepU, step_sound := Taint.stepKeepU_sound }

/-- `taintSym L`, with `umaal` making the registers it writes secret. -/
def taintSymU (L : List String) : VG.Taint isa :=
  { taintSym L with step := Taint.stepKeepSU L, step_sound := Taint.stepKeepSU_sound }

end VG.Arm
