module

public import VerifiedGarbage.Proof.Framework.RISCV64.Inline

/-!
# Frames that allocate a buffer on the stack (RISC-V)

Untrusted: everything here is checked by Lean. A frame `alloc n` … `free n`
(`addi sp, sp, -n` … `addi sp, sp, n`) runs its body from `allocd n s`, with
the stack pointer moved down by `n` and the `n` bytes below the old one a
writable region at the head of `wr`, and ends in `freed n s₂` (`WP.alloc`),
as `WP.frame` (`Call.lean`) does for a frame saving a register.
-/

@[expose] public section

namespace VG.RISCV64

/-- The state an allocating frame's body starts in. -/
def allocd (n : Nat) (s : State) : State :=
  { s with sp := s.sp - BitVec.ofNat 64 n, wr := ⟨s.sp - BitVec.ofNat 64 n, n⟩ :: s.wr }

/-- The state after the frame's `free`, from the state `s` its body ends in. -/
def freed (n : Nat) (s : State) : State :=
  { s with sp := s.sp + BitVec.ofNat 64 n, wr := s.wr.tail }

/-- A frame allocating `n` bytes: its body runs from `allocd n s`, and the
`free` leads to `freed n s₂`. -/
theorem WP.alloc {n : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 0 < n ∧ n < 2048 ∧ n % 16 = 0) (hsp : n ≤ s.sp.toNat)
    (hb : WP isa body (allocd n s) fun s₂ => Q (freed n s₂)) :
    WP isa (.frame (.alloc n) body (.free n)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := hb
  obtain ⟨-, hw, hp⟩ := Exec.rdwr he
  have hpush : isa.push (.alloc n) s = some (allocd n s) := by
    show push (.alloc n) s = some (allocd n s)
    unfold push
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hn.1, hn.2.1, hn.2.2, hsp⟩) |>.trans rfl
  have hpop : isa.pop (.free n) (allocd n s) s₂ = some (freed n s₂) := by
    show pop (.free n) (allocd n s) s₂ = some (freed n s₂)
    unfold pop
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hn.1, hn.2.1, hn.2.2, hp, hw, rfl⟩) |>.trans rfl
  exact ⟨_, _, Exec.frame hpush he hpop, hq⟩

/-- The state after the frame, when its body keeps the permissions and the
stack pointer: those of `s`. -/
theorem freed_eq {n : Nat} {s s₂ : State} (hwr : s₂.wr = (allocd n s).wr)
    (hsp : s₂.sp = (allocd n s).sp) : freed n s₂ = { s₂ with sp := s.sp, wr := s.wr } := by
  simp only [freed, hwr, hsp, allocd, List.tail_cons, BitVec.sub_add_cancel]

end VG.RISCV64
