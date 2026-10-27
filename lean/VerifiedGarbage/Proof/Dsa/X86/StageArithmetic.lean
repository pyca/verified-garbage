module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.CoreProduct
import VerifiedGarbage.Proof.Dsa.X86.CoreSum
public import VerifiedGarbage.Proof.Dsa.X86.CoreReduce
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Scalar arithmetic stages preserve validated caller parameters -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stageProduct_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen) (Rb : OperandReady s base ((qLen + 7) / 8) b qLen)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.product qLen a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen (operandValue s base a qLen * operandValue s base b qLen % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreProduct_ok M.scr M.saved M.room M.extent rfl (by omega) (by omega) (by omega) M.qReady Ra Rb M.qValue
    (by have := M.qLarge; omega) M.qOdd (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base a qLen * operandValue s base b qLen % q) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageProductP_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen + 7) / 8) a pLen) (Rb : OperandReady s base ((pLen + 7) / 8) b pLen)
    (ho : r ≤ output) (hb : output + pLen ≤ usedBytes) :
    WP isa (Core.productMod pLen .p a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output pLen (operandValue s base a pLen * operandValue s base b pLen % p) := by
  have L := M.lengths
  have A := M.aligned
  have N : (pLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreProductMod_ok M.scr M.saved M.room M.extent rfl (by omega) (by omega) (by omega) M.pReady Ra Rb M.pValue
    M.pLarge M.pOdd (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output pLen (operandValue s base a pLen * operandValue s base b pLen % p) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageSum_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen) (Rb : OperandReady s base ((qLen + 7) / 8) b qLen)
    (ha : operandValue s base a qLen < q) (hbb : operandValue s base b qLen < q)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.sum qLen a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen ((operandValue s base a qLen + operandValue s base b qLen) % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreSum_ok M.scr M.saved rfl (by omega) (by omega) (by omega) M.qReady Ra Rb M.qValue
    (by have := M.qLarge; omega) M.qOdd ha hbb (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen ((operandValue s base a qLen + operandValue s base b qLen) % q) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageReduce_ok {base : Addr} {size pLen qLen p q output len : Nat} {s : State} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size ((qLen + 7) / 8) s src len)
    (M : Moduli base size pLen qLen p q s)
    (Ri : StreamInput s base (contextBytes ((qLen + 7) / 8)) (pointerValue base s input) len)
    (hi : len < 2 ^ 32) (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.reduce qLen src input output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output qLen (operandValue s base input len % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreReduce_ok hsrc M.scr M.saved rfl (by omega) (by omega) (by omega) M.qReady Ri hi M.qValue
    M.qLarge M.qOdd (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base input len % q) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

end VG.Proof.Dsa.X86
