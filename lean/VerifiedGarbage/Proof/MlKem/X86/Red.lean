module

public import VerifiedGarbage.Proof.MlKem.X86.Common
public import VerifiedGarbage.Impl.MlKem.X86.Ntt
import VerifiedGarbage.Proof.Framework.X86.Reduce

/-!
# ML-KEM on x86 (32-bit): products

`mul r` multiplies (`wp_mul`, `execMul_eax`, `execMul_other`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Spec.MlKem

/-- `mul r` -/
theorem wp_mul {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) (execMul r s) Q) : WP isa (.block (.mul r :: is)) s Q :=
  wp_cons rfl k

theorem execMul_eax (r : Reg) (s : State) :
    (execMul r s).gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) := by
  simp [execMul, State.setReg, State.setFlags]

theorem execMul_other (r : Reg) (s : State) {x : Reg} (h1 : x ≠ .eax) (h2 : x ≠ .edx) :
    (execMul r s).gpr x = s.gpr x := by
  simp [execMul, State.setReg, State.setFlags, h1, h2]

theorem execMul_only (r : Reg) (s : State) : Only [.eax, .edx] s (execMul r s) :=
  ⟨fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact execMul_other r s hx.1 hx.2, rfl, rfl, rfl⟩

end VG.Proof.MlKem.X86
