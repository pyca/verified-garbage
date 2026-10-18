module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli

/-! # Composing stage frames while retaining immutable caller operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure Execution (base : Addr) (s t : State) : Prop where
  keeps : Keeps powerClob s t
  mem : StackOuts base (s.gpr .esp) runRanges s.mem t.mem

theorem Execution.refl (base : Addr) (s : State) : Execution base s s :=
  ⟨Keeps.refl _ _, StackOuts.refl _ _ _ _⟩

theorem Execution.trans {base : Addr} {s t u : State} (A : Execution base s t) (B : Execution base t u) :
    Execution base s u := by
  refine ⟨A.keeps.trans B.keeps, A.mem.trans ?_⟩
  rw [← A.keeps.1 .esp (by decide)]
  exact B.mem

theorem StageFrame.execution {base : Addr} {s t : State} {output len : Nat}
    (F : StageFrame base s t output len)
    (ho : (r ≤ output ∧ output + len ≤ usedBytes) ∨ (output = Layout.field .mask ∧ len = 4)) :
    Execution base s t := ⟨F.keeps, F.run ho⟩

/-- The saved digest-prefix length is outside every range a run writes. -/
theorem Execution.prefixLen {base : Addr} {s t : State} (E : Execution base s t) :
    pointerValue base t (.input .digestPrefixLen) = pointerValue base s (.input .digestPrefixLen) := by
  apply BitVec.eq_of_toNat_eq
  show w32 t.mem base (VG.Impl.Dsa.X86.Layout.field .digestPrefixLen) =
    w32 s.mem base (VG.Impl.Dsa.X86.Layout.field .digestPrefixLen)
  have V := E.mem.val32 (d := VG.Impl.Dsa.X86.Layout.field .digestPrefixLen) (k := 1) (fun r hr => by
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide) (by decide)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using V

theorem Execution.buffer {base : Addr} {s t : State} {size len : Nat} {p : Pointer}
    (E : Execution base s t) (B : CallerBuffer s base size p len) (hp : StablePointer p) :
    CallerBuffer t base size p len := B.keep E.mem E.keeps (by decide) hp

theorem Execution.value {base : Addr} {s t : State} {size len : Nat} {p : Pointer}
    (E : Execution base s t) (B : CallerBuffer s base size p len) (hp : StablePointer p) (hz : usedBytes ≤ size) :
    operandValue t base p len = operandValue s base p len :=
  B.value_keep E.mem E.keeps (by decide) hp hz

end VG.Proof.Dsa.X86
