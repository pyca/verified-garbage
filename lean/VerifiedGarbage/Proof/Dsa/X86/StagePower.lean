module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.CorePower

/-! # Fixed-iteration powers preserving validated DSA inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stagePowerP_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a e : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen + 7) / 8) a pLen)
    (Re : OperandReady s base ((pLen + 7) / 8) e qLen)
    (ho : r ≤ output) (hb : output + pLen ≤ usedBytes) :
    WP isa (Core.power pLen qLen .p a e output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output pLen (operandValue s base a pLen ^ operandValue s base e qLen % p) := by
  have L := M.lengths
  have A := M.aligned
  have N : (pLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (corePower_ok M.scr M.saved M.room M.extent rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    M.pReady Ra Re M.pValue M.pLarge M.pOdd (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output pLen (operandValue s base a pLen ^ operandValue s base e qLen % p) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stagePowerQ_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a e : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen)
    (Re : OperandReady s base ((qLen + 7) / 8) e qLen)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.power qLen qLen .q a e output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen (operandValue s base a qLen ^ operandValue s base e qLen % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (corePower_ok M.scr M.saved M.room M.extent rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    M.qReady Ra Re M.qValue (by have := M.qLarge; omega) M.qOdd (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base a qLen ^ operandValue s base e qLen % q) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

end VG.Proof.Dsa.X86
