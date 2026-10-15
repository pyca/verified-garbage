module

public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# A block as the sequence of its parts

The kernel shares the analysis of equal blocks from the same taint
(`materialize_shared`, `Proof/Framework/LitShare.lean`), but not of equal
stretches of one block. Code emitted as one block whose parts repeat (field
operations on different slots, the same once their displacements are erased:
`Proof/Framework/X86/TaintErase.lean`) is checked as the sequence of its parts
instead: `Code.splitBlock ns is` cuts `is` into parts of the lengths `ns` (the
rest last), which runs as the block does and leaks the same trace
(`Exec.splitBlock`), so it is constant time only if the block is
(`ConstantTime.of_splitBlock`).
-/

@[expose] public section

namespace VG

/-- The block `is` as the sequence of its parts of lengths `ns`, and the rest. -/
def Code.splitBlock {I C : Type} : List Nat → List I → Code I C
  | [], is => .block is
  | n :: ns, is => .seq (.block (is.take n)) (splitBlock ns (is.drop n))

/-- `c` with its parts cut as `Code.splitBlock ns`, if it is a block. -/
def Code.split {I C : Type} (ns : List Nat) : Code I C → Code I C
  | .block is => splitBlock ns is
  | c => c

variable {M : ISA}

/-- A run of the block is a run of its parts, with the same trace. -/
theorem Exec.splitBlock : ∀ (ns : List Nat) {is : List M.Instr} {s s' : M.State} {t : List Leak},
    Exec M (.block is) s t s' → Exec M (Code.splitBlock ns is) s t s'
  | [], _, _, _, _, h => h
  | n :: ns, is, s, s', t, h => by
    rw [Exec.block_iff, ← List.take_append_drop n is, execBlock_append] at h
    obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨b, w⟩, hc, he⟩ := Option.map_eq_some_iff.mp hb
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (.block ha) (Exec.splitBlock ns (.block hc))

/-- A block is constant time if the sequence of its parts is. -/
theorem ConstantTime.of_splitBlock {Pre : M.State → Prop} {Pub : M.State → M.State → Prop}
    (ns : List Nat) {is : List M.Instr} (h : ConstantTime M Pre Pub (Code.splitBlock ns is)) :
    ConstantTime M Pre Pub (.block is) :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => h _ _ _ _ _ _ h₁ h₂ hp (Exec.splitBlock ns e₁) (Exec.splitBlock ns e₂)

/-- Code is constant time if its parts are. -/
theorem ConstantTime.of_split {Pre : M.State → Prop} {Pub : M.State → M.State → Prop}
    (ns : List Nat) {c : Prog M} (h : ConstantTime M Pre Pub (Code.split ns c)) :
    ConstantTime M Pre Pub c := by
  cases c with
  | block is => exact ConstantTime.of_splitBlock ns h
  | _ => exact h

end VG
