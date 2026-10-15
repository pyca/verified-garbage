module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli

/-! # Composing stage frames while retaining immutable caller operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure Execution (base : Addr) (s t : State) : Prop where
  keeps : Keeps powerClob s t
  mem : Outs base runRanges s.mem t.mem

theorem Execution.refl (base : Addr) (s : State) : Execution base s s :=
  ⟨Keeps.refl _ _, Outs.refl _ _ _⟩

theorem Execution.trans {base : Addr} {s t u : State} (A : Execution base s t) (B : Execution base t u) :
    Execution base s u := ⟨A.keeps.trans B.keeps, A.mem.trans B.mem⟩

theorem StageFrame.execution {base : Addr} {s t : State} {output len : Nat}
    (F : StageFrame base s t output len)
    (ho : (r ≤ output ∧ output + len ≤ usedBytes) ∨ (output = Layout.field .mask ∧ len = 4)) :
    Execution base s t := ⟨F.keeps, F.run ho⟩

theorem Execution.buffer {base : Addr} {s t : State} {size len : Nat} {p : Pointer}
    (E : Execution base s t) (B : CallerBuffer s base size p len) (hp : StablePointer p) :
    CallerBuffer t base size p len := B.keep E.mem E.keeps (by decide) hp

theorem Execution.value {base : Addr} {s t : State} {size len : Nat} {p : Pointer}
    (E : Execution base s t) (B : CallerBuffer s base size p len) (hp : StablePointer p) (hz : usedBytes ≤ size) :
    operandValue t base p len = operandValue s base p len :=
  B.value_keep E.mem E.keeps (by decide) hp hz

end VG.Proof.Dsa.X86
