module

public import VerifiedGarbage.Proof.Framework.Slh
public import VerifiedGarbage.Proof.Framework.X86_64.Spectre
import VerifiedGarbage.Proof.Framework.X86_64.Fence
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Speculative load hardening on x86-64 (prototype)

The prologue at a branch target is `cmovcc r, rsp` for each register `r` of
`rs`, with the condition under which the branch was mispredicted: `cmov¬c`
where the branch went because `c` holds (`pt`), `cmovc` where it did not
(`pe`). Where the branch was predicted correctly the `cmov`s do nothing
(`execCmov` returns the state itself; "Flags Affected: None"), and where it
was mispredicted they set each `r` to `rsp`, which both runs agree on (`Inv`:
the calling convention's `pub` says so on entry, and the stack pointer moves
alike along the same path). So after the prologue, the registers `rs` and
`rsp` are public (`τR`), whatever the runs held before.

`slhOk` discharges `SlhOk` for the transient semantics `Spectre.spectre`.
-/

@[expose] public section

namespace VG.X86_64.Slh

open VG.X86_64

/-- The opposite condition. -/
def neg : Cond → Cond
  | .e => .ne
  | .ne => .e
  | .b => .ae
  | .ae => .b

theorem eval_neg (c : Cond) (s : State) : eval (neg c) s = (eval c s).map (!·) := by
  cases c <;> simp only [neg, eval, Option.map_map] <;> cases s.zf <;> cases s.cf <;>
    simp [Function.comp_def]

/-- `cmovc r, rsp` for each `r` of `rs`. -/
def protect (c : Cond) (rs : List Reg) : List Instr := rs.map fun r => .cmov c r (.reg .rsp)

/-- The prologue where the branch went because `c` holds. -/
def pt (rs : List Reg) (c : Cond) : List Instr := protect (neg c) rs

/-- The prologue where the branch went because `c` does not hold. -/
def pe (rs : List Reg) (c : Cond) : List Instr := protect c rs

/-- The stack pointers agree. -/
def Inv (s₁ s₂ : State) : Prop := s₁.gpr .rsp = s₂.gpr .rsp

/-- What the prologue makes public. -/
def τR (rs : List Reg) : Taint.T := Taint.ofRegs (.rsp :: rs)

theorem protect_nop {c : Cond} {s : State} (h : eval c s = some false) (rs : List Reg) :
    execBlock isa (protect c rs) s = some (s, []) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [protect, List.map_cons, execBlock] at ih ⊢
    have : exec (.cmov c r (.reg .rsp)) s = some s := by
      simp only [exec, execCmov, readSrc, Option.bind_some, h, Option.map_some, Bool.false_eq_true,
        ↓reduceIte]
    rw [this]
    dsimp only
    rw [ih]
    simp [addrs, srcAddrs]

theorem pt_nop (rs : List Reg) (c : Cond) (s : State) (h : eval c s = some true) :
    execBlock isa (pt rs c) s = some (s, []) :=
  protect_nop (by rw [eval_neg, h]; rfl) rs

theorem pe_nop (rs : List Reg) (c : Cond) (s : State) (h : eval c s = some false) :
    execBlock isa (pe rs c) s = some (s, []) :=
  protect_nop h rs

theorem eval_widen (c : Cond) (s : State) : eval c (Spectre.widen s) = eval c s := by
  cases c <;> rfl

theorem eval_setReg (c : Cond) (s : State) (r : Reg) (v : BitVec 64) :
    eval c (s.setReg r v) = eval c s := by
  cases c <;> rfl

/-- The prologue, run transiently where it fires: every register of `rs`
becomes `rsp`. -/
theorem protect_tr {c : Cond} (rs : List Reg) (hrs : .rsp ∉ rs) :
    ∀ {acc : List Reg} {s₁ s₂ : State} {n : Nat} {t₁ t₂ : List SLeak} {r₁ r₂ : Option (State × Nat)},
      s₁.gpr .rsp = s₂.gpr .rsp → eval c s₁ = some true → eval c s₂ = some true →
      (∀ r ∈ acc, s₁.gpr r = s₂.gpr r) →
      SBlock Spectre.spectre (protect c rs) s₁ true n t₁ r₁ →
      SBlock Spectre.spectre (protect c rs) s₂ true n t₂ r₂ →
      t₁ = t₂ ∧ (r₁ = none ∧ r₂ = none ∨ ∃ a b k, r₁ = some (a, k) ∧ r₂ = some (b, k) ∧
        a.gpr .rsp = b.gpr .rsp ∧ ∀ r ∈ acc ++ rs, a.gpr r = b.gpr r) := by
  induction rs with
  | nil =>
    intro acc s₁ s₂ n t₁ t₂ r₁ r₂ hsp _ _ hacc e₁ e₂
    obtain ⟨rfl, rfl⟩ := sblock_nil_inv e₁
    obtain ⟨rfl, rfl⟩ := sblock_nil_inv e₂
    exact ⟨rfl, .inr ⟨_, _, _, rfl, rfl, hsp, by simpa using hacc⟩⟩
  | cons r rs ih =>
    intro acc s₁ s₂ n t₁ t₂ r₁ r₂ hsp hc₁ hc₂ hacc e₁ e₂
    simp only [List.mem_cons, not_or] at hrs
    have hr : r ≠ .rsp := fun h => hrs.1 h.symm
    have hfence : Spectre.spectre.fence (.cmov c r (.reg .rsp)) = false := rfl
    rcases sblock_cons_inv e₁ with ⟨rfl, rfl, rfl⟩ | ⟨-, h, -⟩ | ⟨u₁, k₁, t₁', -, rfl, x₁, b₁, rfl⟩
    · rcases sblock_cons_inv e₂ with h₂ | h₂ | h₂
      · obtain ⟨-, rfl, rfl⟩ := h₂; exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
      · obtain ⟨-, h, -⟩ := h₂; rw [hfence] at h; cases h
      · obtain ⟨_, _, _, _, hn, _⟩ := h₂; cases hn
    · rw [hfence] at h; cases h
    · rcases sblock_cons_inv e₂ with h₂ | h₂ | ⟨u₂, k₂, t₂', -, hk, x₂, b₂, rfl⟩
      · obtain ⟨h, -⟩ := h₂; cases h
      · obtain ⟨-, h, -⟩ := h₂; rw [hfence] at h; cases h
      · cases hk
        simp only [VG.Spectre.run, ↓reduceIte, Spectre.spectre, Spectre.tstore, Option.none_or,
          isa, exec, execCmov, readSrc, Option.bind_some, eval_widen, hc₁, hc₂, Option.map_some,
          ↓reduceIte, Option.some.injEq] at x₁ x₂
        subst x₁ x₂
        obtain ⟨ht, hq⟩ := ih hrs.2 (acc := acc ++ [r])
          (by simp only [State.setReg, hr.symm, ↓reduceIte]; exact hsp)
          (by rw [eval_setReg, eval_widen, hc₁]) (by rw [eval_setReg, eval_widen, hc₂])
          (by
            intro x hx
            simp only [List.mem_append, List.mem_singleton] at hx
            by_cases hxr : x = r
            · subst hxr; simp only [State.setReg, ↓reduceIte]; exact hsp
            · simp only [State.setReg, hxr, ↓reduceIte]
              exact hacc x (hx.resolve_right hxr))
          b₁ b₂
        refine ⟨by rw [ht], ?_⟩
        rw [List.append_assoc, List.singleton_append] at hq
        exact hq

theorem protect_rel {c : Cond} {rs : List Reg} (hrs : .rsp ∉ rs) {s₁ s₂ : State} {n : Nat}
    {t₁ t₂ : List SLeak} {r₁ r₂ : Option (State × Nat)} (hi : Inv s₁ s₂)
    (hc₁ : eval c s₁ = some true) (hc₂ : eval c s₂ = some true)
    (e₁ : SBlock Spectre.spectre (protect c rs) s₁ true n t₁ r₁)
    (e₂ : SBlock Spectre.spectre (protect c rs) s₂ true n t₂ r₂) :
    t₁ = t₂ ∧ VG.Taint.BRel taint (τR rs) r₁ r₂ := by
  obtain ⟨ht, h⟩ := protect_tr rs hrs (acc := []) hi hc₁ hc₂ nofun e₁ e₂
  refine ⟨ht, ?_⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨a, b, k, rfl, rfl, hsp, hr⟩
  · trivial
  · refine ⟨rfl, Taint.agree_ofRegs fun r hr' => ?_⟩
    simp only [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact hsp
    · exact hr r (by simpa using hr')

theorem push_rsp {i : Instr} {s₁ s₂ s₁' s₂' : State} (hi : Inv s₁ s₂)
    (h₁ : isa.push i s₁ = some s₁') (h₂ : isa.push i s₂ = some s₂') : Inv s₁' s₂' := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h₁ h₂
  case push rs =>
    split at h₁ <;> cases h₁
    split at h₂ <;> cases h₂
    show (pushRegs s₁ rs).gpr .rsp = (pushRegs s₂ rs).gpr .rsp
    rw [(pushRegs_eq s₁ rs).2.2.1, (pushRegs_eq s₂ rs).2.2.1, hi]
  case alloc bytes =>
    split at h₁ <;> cases h₁
    split at h₂ <;> cases h₂
    simp only [Inv, State.setReg, ↓reduceIte]; rw [hi]

theorem pop_rsp {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (hi : Inv b₁ b₂)
    (h₁ : isa.pop j a₁ b₁ = some c₁) (h₂ : isa.pop j a₂ b₂ = some c₂) : Inv c₁ c₂ := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h₁ h₂
  case pop r k =>
    split at h₁ <;> cases h₁
    split at h₂ <;> cases h₂
    show (popReg b₁ r k).gpr .rsp = (popReg b₂ r k).gpr .rsp
    rw [(popReg_eq b₁ r k).2.2.1, (popReg_eq b₂ r k).2.2.1, hi]
  case free bytes =>
    split at h₁ <;> cases h₁
    split at h₂ <;> cases h₂
    simp only [Inv, State.setReg, ↓reduceIte]; rw [hi]

/-- **Hardening x86-64 code** with `cmov`s of `rsp` into the registers `rs`
meets `SlhOk` for the transient semantics `Spectre.spectre`. -/
theorem slhOk {rs : List Reg} (hrs : .rsp ∉ rs) :
    SlhOk Spectre.spectre taint (τR rs) (pt rs) (pe rs) Inv (fun i => !isa.writesSp i) where
  shape := leakShape
  sound := Spectre.specSound
  pro := {
    pt := fun hi h₁ h₂ e₁ e₂ =>
      protect_rel hrs hi (by rw [eval_neg]; exact congrArg (Option.map _) h₁)
        (by rw [eval_neg]; exact congrArg (Option.map _) h₂) e₁ e₂
    pe := fun hi h₁ h₂ e₁ e₂ => protect_rel hrs hi h₁ h₂ e₁ e₂ }
  pt_nop := pt_nop rs
  pe_nop := pe_nop rs
  exec := by
    intro i s₁ s₂ s₁' s₂' hp hi e₁ e₂
    have hw : isa.writesSp i = false := by simpa using hp
    simp only [Inv]; rw [exec_rsp hw e₁, exec_rsp hw e₂]; exact hi
  call := fun hi e₁ e₂ => by
    simp only [isa, call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    simp only [Inv, State.setReg, ↓reduceIte]; rw [hi]
  ret := fun hi e₁ e₂ => by
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> cases e₁
    split at e₂ <;> cases e₂
    simp only [Inv, State.setReg, ↓reduceIte]; rw [hi]
  push := push_rsp
  pop := pop_rsp

end VG.X86_64.Slh
