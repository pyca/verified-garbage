module
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Dsa.X86.Validate

import VerifiedGarbage.Proof.Dsa.X86.ValidateMinus
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Persistent modulus-minus-constant stages -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stageMinusP_ok {base : Addr} {size pLen qLen p q amount output : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (ha : amount ≤ p)
    (ho : r ≤ output) (hb : output + pLen ≤ usedBytes) :
    WP isa (Validate.minus pLen .p amount output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output pLen (p - amount) := by
  have L := M.lengths
  have A := M.aligned
  have N : (pLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (validateMinus_ok M.scr M.saved rfl (by omega) (by omega) (by omega) M.pReady M.pValue
    ha (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output pLen (p - amount) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageMinusQ_ok {base : Addr} {size pLen qLen p q amount output : Nat} {s : State}
    (M : Moduli base size pLen qLen p q s) (ha : amount ≤ q)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Validate.minus qLen .q amount output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output qLen (q - amount) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (validateMinus_ok M.scr M.saved rfl (by omega) (by omega) (by omega) M.qReady M.qValue
    ha (Nat.le_trans hb M.extent) (by omega)) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (q - amount) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

end VG.Proof.Dsa.X86
