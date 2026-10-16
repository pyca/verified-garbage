module

public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# x86-64: alignment padding in correctness and constant-time proofs

`Instr.align` executes as a NOP and accesses no memory, so code with the
padding in front of it, or at the end of a block, satisfies what the code
without it does, and leaks the same trace.
-/

@[expose] public section

namespace VG.X86_64

theorem WP.align {k : Nat} {s : State} {Q : State → Prop} (h : Q s) :
    WP isa (.block [.align k]) s Q :=
  WP.of_runBlock ⟨s, by rw [runBlock_align, runBlock_nil], h⟩

theorem WP.align_seq {k : Nat} {p : Prog isa} {s : State} {Q : State → Prop} (h : WP isa p s Q) :
    WP isa (.seq (.block [.align k]) p) s Q :=
  WP.seq (WP.align h)

theorem WP.append_align {k : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block is) s Q) : WP isa (.block (is ++ [.align k])) s Q :=
  WP.block_append_iff.mpr (WP.mono h fun _ ht => WP.align ht)

theorem RelCT.align {k : Nat} {P : State → State → Prop} :
    RelCT isa P (.block [.align k]) P := by
  intro x y t₁ t₂ x' y' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, exec, addrs, List.map_nil, List.nil_append, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, hp⟩

theorem RelCT.align_seq {k : Nat} {P Q : State → State → Prop} {p : Prog isa}
    (h : RelCT isa P p Q) : RelCT isa P (.seq (.block [.align k]) p) Q :=
  RelCT.seq RelCT.align h

end VG.X86_64
