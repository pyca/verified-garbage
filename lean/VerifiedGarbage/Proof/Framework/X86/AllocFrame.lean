module

import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# Frames of stack the code allocates (x86, 32-bit)

`frame (alloc n) body (free n)` moves `esp` down `n` bytes, which become a
writable region, the first of `wr`, runs `body`, and moves `esp` back up,
removing the region (`TCB/X86/Isa.lean`). Code passes a call more arguments
than it has registers to push by storing them into such a frame, at `esp`
and above, before the call. `WP.frameAlloc` runs a body from the state after
the allocation (`allocFrame`) to the state after the frame (`freed`), and
`RelCT.frameAlloc` relates two runs of it, whose allocation and freeing
access no memory.
-/

@[expose] public section

namespace VG.X86

/-- The state after a frame's allocation of `bytes` bytes. -/
def allocFrame (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 bytes) with
    wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr }

/-- The state after the frame's freeing of `bytes` bytes, from the state `s` its body ends in. -/
def freed (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp + BitVec.ofNat 32 bytes) with wr := s.wr.tail }

@[simp] theorem allocFrame_esp (bytes : Nat) (s : State) :
    (allocFrame bytes s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 bytes := by
  simp [allocFrame, State.setReg]
@[simp] theorem allocFrame_mem (bytes : Nat) (s : State) : (allocFrame bytes s).mem = s.mem := rfl
@[simp] theorem allocFrame_rd (bytes : Nat) (s : State) : (allocFrame bytes s).rd = s.rd := rfl
@[simp] theorem allocFrame_wr (bytes : Nat) (s : State) :
    (allocFrame bytes s).wr = ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr := rfl
theorem allocFrame_gpr (bytes : Nat) (s : State) {q : Reg} (h : q ≠ .esp) :
    (allocFrame bytes s).gpr q = s.gpr q := by
  simp [allocFrame, State.setReg, h]

@[simp] theorem freed_esp (bytes : Nat) (s : State) :
    (freed bytes s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 bytes := by
  simp [freed, State.setReg]
@[simp] theorem freed_mem (bytes : Nat) (s : State) : (freed bytes s).mem = s.mem := rfl
@[simp] theorem freed_rd (bytes : Nat) (s : State) : (freed bytes s).rd = s.rd := rfl
@[simp] theorem freed_wr (bytes : Nat) (s : State) : (freed bytes s).wr = s.wr.tail := rfl
theorem freed_gpr (bytes : Nat) (s : State) {q : Reg} (h : q ≠ .esp) : (freed bytes s).gpr q = s.gpr q := by
  simp [freed, State.setReg, h]

theorem alloc_some {bytes : Nat} {s s₁ : State} (h : isa.push (.alloc bytes) s = some s₁) :
    s₁ = allocFrame bytes s := by
  simp only [isa, push] at h
  split at h <;> [cases h; cases h]
  rfl

/-- A frame of `bytes` bytes: its body, which never writes `esp`, runs from
`allocFrame bytes s`, and the frame's freeing leads to `freed bytes s₂`. -/
theorem WP.frameAlloc {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (h0 : 0 < bytes) (h1 : bytes < 4096) (h4 : bytes % 4 = 0) (hn : bytes ≤ (s.gpr .esp).toNat)
    (hsp : NoSp body) (hb : WP isa body (allocFrame bytes s) fun s₂ => Q (freed bytes s₂)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hsp he
  have hpush : isa.push (.alloc bytes) s = some (allocFrame bytes s) := by
    simp only [isa, push, h0, h1, h4, hn, and_self, ite_true]
    rfl
  have hpop : isa.pop (.free bytes) (allocFrame bytes s) s₂ = some (freed bytes s₂) := by
    simp only [isa, pop]
    refine ite_eq_left ⟨h0, h1, h4, hp, hw, ?_⟩
    simp
  exact ⟨_, _, Exec.frame hpush he hpop, hq⟩

/-- Two runs of a frame of `bytes` bytes leak the same trace when the runs of
its body, from the states after the allocation, do. -/
theorem RelCT.frameAlloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocFrame bytes s₁ ∧ b = allocFrame bytes s₂) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea := alloc_some p₁
      have eb := alloc_some p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

end VG.X86
