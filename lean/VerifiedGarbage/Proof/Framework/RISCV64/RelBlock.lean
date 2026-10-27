module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Relating two runs of straight-line code (RISC-V)

The pieces a relational constant-time proof composes besides calls
(`RelCT.call`, `Proof/Framework/RISCV64/RelCT.lean`): a block the taint
analysis checks from registers on which the runs agree (`taint_block`), a
block that accesses no memory, which leaks nothing (`relct_noMem`), the empty
block (`relct_nil`), and a piece whose final states the correctness proofs
describe (`relct_wp`). As ML-KEM's on PPC64LE (`Proof/MlKem/PPC64LE/SampleCT.lean`,
`Proof/Ed448/PPC64LE/Whole/HashCT.lean`).
-/

@[expose] public section

namespace VG.RISCV64

/-- A block the taint analysis checks from the registers `rs`, on which the runs agree. -/
theorem taint_block {P : State → State → Prop} {is : List Instr} (rs : List Reg)
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun a b hab => ⟨hsp a b hab, fun r hr => hP a b hab r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A piece whose final states in the two runs the correctness proofs describe. -/
theorem relct_wp {c : Prog isa} {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .load .. | .store .. | .push _ | .pop _ => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : noMem i = true) (s : State) : addrs i s = [] := by
  cases i <;> first | rfl | simp [noMem] at h

theorem execBlock_noMem : ∀ {is : List Instr}, is.all noMem = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → t = []
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | i :: is, hm, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hm
    simp only [execBlock] at h
    split at h
    · cases h
    · obtain ⟨⟨s'', t'⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
      cases h₂
      rw [addrs_noMem hm.1 s]
      simpa using execBlock_noMem hm.2 h₁

/-- A block that accesses no memory leaks nothing. -/
theorem relct_noMem {P : State → State → Prop} {is : List Instr} (h : is.all noMem = true) :
    RelCT isa P (.block is) fun _ _ => True := fun _ _ _ _ _ _ _ e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  rw [execBlock_noMem h e₁, execBlock_noMem h e₂]; exact ⟨rfl, trivial⟩

/-- The empty block. -/
theorem relct_nil {P : State → State → Prop} : RelCT isa P (.block []) P := fun _ _ _ _ _ _ hp e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

end VG.RISCV64
