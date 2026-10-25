module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Taint tracking for RISC-V

Untrusted: everything here is checked by Lean.

The abstract state is the set of registers known to be public; the stack
pointer is always public. The address of a static (`lla`) is secret here;
`taintSym` (`TaintSym.lean`) makes those the contract lists public. Memory
is always secret: a loaded value is secret, and an address must be computed
from a public register. A call leaves
unknown values in `ra` and `t0`–`t6`, which become secret.
-/

@[expose] public section

namespace VG.RISCV64.Taint

deriving instance Lean.ToExpr for Reg

instance : RegIdx Reg := ⟨Reg.ctorIdx, fun {a b} h => by rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]⟩

abbrev T := RegSet Reg

def pub (τ : T) (r : Reg) : Bool := τ.mem r

/-- Exactly the registers `rs` are public. -/
def ofRegs (rs : List Reg) : T := RegSet.ofList rs

@[simp] theorem mem_ofRegs {rs : List Reg} {r : Reg} : r ∈ ofRegs rs ↔ r ∈ rs := RegSet.mem_ofList

def Agree (τ : T) (s₁ s₂ : State) : Prop := s₁.sp = s₂.sp ∧ ∀ r ∈ τ, s₁.gpr r = s₂.gpr r

/-- The public registers after writing `r`, with a public value iff `p`. -/
def set (τ : T) (r : Reg) (p : Bool) : T :=
  if p then τ.insert r else τ.erase r

def step (τ : T) : Instr → Option T
  | .add d n m | .sub d n m | .addw d n m | .subw d n m | .sltu d n m | .mul d n m
  | .mulhu d n m | .logic _ d n m =>
    some (set τ d (pub τ n && pub τ m))
  | .addi d n _ | .addiw d n _ | .logicImm _ d n _ | .shift _ _ d n _ => some (set τ d (pub τ n))
  | .li d _ | .lui d _ => some (set τ d true)
  -- The stack pointer is public.
  | .addSp d _ => some (set τ d true)
  | .load _ t n _ => if pub τ n then some (set τ t false) else none
  | .store _ _ n _ => if pub τ n then some τ else none
  -- The address of a static is secret, unless the contract makes it public
  -- (`taintSym`).
  | .lla d _ => some (set τ d false)
  -- Frames are analysed by `push` and `pop`.
  | .push .. | .pop .. | .alloc .. | .free .. => none

def condPub (τ : T) : Cond → Bool
  | .zero r | .nonzero r => pub τ r
  | .eq a b | .ne a b | .ltu a b | .geu a b => pub τ a && pub τ b

theorem pub_iff {τ : T} {r : Reg} : pub τ r = true ↔ r ∈ τ := Iff.rfl

theorem Agree.reg {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) {r : Reg} (hr : pub τ r = true) :
    s₁.gpr r = s₂.gpr r := h.2 r (pub_iff.mp hr)

theorem Agree.write {τ : T} {s₁ s₂ : State} (h : Agree τ s₁ s₂) (d : Reg) {p : Bool}
    {v₁ v₂ : BitVec 64} (hv : p = true → v₁ = v₂) :
    Agree (set τ d p) (s₁.write d v₁) (s₂.write d v₂) := by
  refine ⟨h.1, fun r hr => ?_⟩
  simp only [State.write]
  unfold set at hr
  by_cases hp : p = true
  · simp only [hp, ite_true, RegSet.mem_insert] at hr
    by_cases hrd : r = d
    · simp [hrd, hv hp]
    · simp [hrd, h.2 r (hr.resolve_left hrd)]
  · simp only [hp, Bool.false_eq_true, ite_false, RegSet.mem_erase] at hr
    simp [hr.1, h.2 r hr.2]

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | push | pop | alloc | free => simp only [step, reduceCtorEq] at hs
  | lla d name =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write d fun h => by cases h⟩
  | addSp d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.write d fun _ => by rw [ha.1]⟩
  | add d n m | sub d n m | addw d n m | subw d n m | sltu d n m | mul d n m | mulhu d n m
  | logic op d n m =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    refine ⟨rfl, ha.write d fun hp => ?_⟩
    simp only [Bool.and_eq_true] at hp
    rw [ha.reg hp.1, ha.reg hp.2]
  | addi d n imm | addiw d n imm | logicImm op d n imm | li d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
    cases e₁; cases e₂
    first
    | exact ⟨rfl, ha.write d fun hp => by rw [ha.reg hp]⟩
    | exact ⟨rfl, ha.write d fun _ => rfl⟩
  | shift op sz d n sh =>
    simp only [step, Option.some.injEq] at hs; subst hs
    cases sz <;>
    · simp only [exec] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      rename_i h
      rw [ite_eq_left_of_eq_true _ _ (eq_true h)] at e₂
      cases e₁; cases e₂
      exact ⟨rfl, ha.write d fun hp => by rw [ha.reg hp]⟩
  | lui d imm =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write d fun _ => rfl⟩
  | load wd t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, -, v₁, -, rfl⟩ := e₁; obtain ⟨a₂, -, v₂, -, rfl⟩ := e₂
    exact ha.write t fun h => by cases h
  | store wd t n off =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hn; cases hs
    refine ⟨by simp [addrs, ha.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨a₁, -, e₁⟩ := e₁; obtain ⟨a₂, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : condPub τ c = true) : eval c s₁ = eval c s₂ := by
  cases c <;> simp only [condPub, Bool.and_eq_true] at hc
  · simp [eval, ha.reg hc]
  · simp [eval, ha.reg hc]
  all_goals simp [eval, ha.reg hc.1, ha.reg hc.2]

/-- A frame's push stores to memory, which is secret. -/
def push (τ : T) : Instr → Option T
  | .push _ | .alloc _ => some τ
  | _ => none

/-- A frame's pop loads a secret. -/
def pop (τ : T) : Instr → Option T
  | .pop r => some (τ.erase r)
  | .free _ => some τ
  | _ => none

theorem push_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (h : Agree τ s₁ s₂)
    (hs : push τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂') :
    isa.addrs i s₁ = isa.addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i <;> simp only [push, reduceCtorEq] at hs <;> cases hs <;>
  · simp only [isa, RISCV64.push] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨by simp [addrs, h.1], by simp [h.1], h.2⟩

theorem pop_sound {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (h : Agree τ b₁ b₂)
    (hs : pop τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂) :
    isa.addrs j b₁ = isa.addrs j b₂ ∧ Agree τ' c₁ c₂ := by
  cases j <;> simp only [pop, reduceCtorEq] at hs
  case free =>
    cases hs
    simp only [isa, RISCV64.pop] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, by simp [h.1], h.2⟩
  rename_i r
  cases hs
  simp only [isa, RISCV64.pop] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  refine ⟨by simp [addrs, h.1], by simp [h.1], fun r' hr' => ?_⟩
  simp only [RegSet.mem_erase] at hr'
  simp [State.write, hr'.1, h.2 r' hr'.2]

/-- The registers a call leaves unknown values in: the return address in
`ra`, and `t0`–`t6`. -/
def callErase (τ : T) : T :=
  ((((((((τ.erase .ra).erase .t0).erase .t1).erase .t2).erase .t3).erase .t4).erase .t5).erase .t6)

theorem mem_callErase {τ : T} {r : Reg} :
    r ∈ callErase τ ↔ r ≠ .t6 ∧ r ≠ .t5 ∧ r ≠ .t4 ∧ r ≠ .t3 ∧ r ≠ .t2 ∧ r ≠ .t1 ∧ r ≠ .t0 ∧
      r ≠ .ra ∧ r ∈ τ := by
  simp only [callErase, RegSet.mem_erase]

end VG.RISCV64.Taint

namespace VG.RISCV64

/-- Taint tracking for RISC-V. -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.step
  step_sound := Taint.step_sound
  condPub := Taint.condPub
  cond_sound := Taint.cond_sound
  meet τ₁ τ₂ := τ₁.inter τ₂
  meet_left h := ⟨h.1, fun r hr => h.2 r (RegSet.mem_inter.mp hr).1⟩
  meet_right h := ⟨h.1, fun r hr => h.2 r (RegSet.mem_inter.mp hr).2⟩
  le τ σ := τ.subset σ
  le_sound hle h := ⟨h.1, fun r hr => h.2 r (RegSet.mem_of_subset hle hr)⟩
  -- A call leaves unknown values in `ra` and `t0`–`t6`; a return changes
  -- nothing.
  call τ := some (Taint.callErase τ)
  call_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    refine ⟨rfl, h.1, fun r hr => ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hr⟩ := Taint.mem_callErase.mp hr
    cases r <;> first | exact absurd rfl ‹_› | exact h.2 _ hr
  ret τ := some τ
  ret_sound h hs e₁ e₂ := by
    cases hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ⟨rfl, h⟩
  -- A frame's push stores to memory, which is secret; its pop loads a secret.
  push := Taint.push
  push_sound := Taint.push_sound
  pop := Taint.pop
  pop_sound := Taint.pop_sound

end VG.RISCV64
