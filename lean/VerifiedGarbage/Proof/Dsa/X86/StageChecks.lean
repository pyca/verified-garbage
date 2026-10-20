module
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame

import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.ValidateRange
import VerifiedGarbage.Proof.Dsa.X86.ValidateEqual
import VerifiedGarbage.Proof.Dsa.X86.ValidateOne
import VerifiedGarbage.Proof.Dsa.X86.ValidateZero
import VerifiedGarbage.Proof.Dsa.X86.StageValues
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Validation stages preserve moduli and persistent intermediate values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem stageRange_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {input : Pointer} {modulus : Field}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rm : OperandReady s base ((len + 7) / 8) (.input modulus) len)
    (Ri : OperandReady s base ((len + 7) / 8) input len) (aboveOne : Bool) :
    WP isa (Validate.range len modulus input aboveOne) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        ((if aboveOne then 1 else 0) < operandValue s base input len ∧ operandValue s base input len < operandValue s base (.input modulus) len) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateRange_ok M.scr M.saved rfl h4 hmax hw4 Rm Ri aboveOne) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega)
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem stageEqual_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Ra : OperandReady s base ((len + 7) / 8) a len)
    (Rb : OperandReady s base ((len + 7) / 8) b len) :
    WP isa (Validate.equalValues len a b) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (operandValue s base a len = operandValue s base b len) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateEqual_ok M.scr M.saved rfl h4 hmax hw4 Ra Rb) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega)
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem stageOne_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {input : Pointer}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base ((len + 7) / 8) input len) :
    WP isa (Validate.isOne len input) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (operandValue s base input len = 1) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateOne_ok M.scr M.saved rfl h4 hmax hw4 R) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega)
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem stageZero_ok {base : Addr} {size pLen qLen p q len : Nat} {s : State} {input : Pointer}
    (M : Moduli base size pLen qLen p q s) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (R : OperandReady s base ((len + 7) / 8) input len) (wantNonzero : Bool) :
    WP isa (Validate.zero len input wantNonzero) s fun t =>
      Moduli base size pLen qLen p q t ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s &&& mask32
        (if wantNonzero then operandValue s base input len ≠ 0 else operandValue s base input len = 0) ∧ StageFrame base s t (Layout.field .mask) 4 := by
  refine WP.mono (validateZero_ok M.scr M.saved rfl h4 hmax hw4 R wantNonzero) fun t ⟨V, K, O⟩ => ?_
  have F := StageFrame.of_frame K (by decide) O (by omega)
  exact ⟨M.keep (F.run (.inr ⟨rfl, rfl⟩)) F.keeps (by decide) (by decide), V, F⟩

theorem StageFrame.scalar_keep_mask {base : Addr} {size pLen qLen p q d : Nat} {s t : State}
    (F : StageFrame base s t (Layout.field .mask) 4) (M : Moduli base size pLen qLen p q s)
    (hd : d ∈ Layout.scalars) :
    operandValue t base (.local d) qLen = operandValue s base (.local d) qLen := by
  have H := VG.Proof.Dsa.X86.Layout.scalar_bounds hd
  exact F.local_value_keep M.scr (by have := M.lengths; omega)
    (by change 7048 ≤ d; omega) (Nat.le_trans (M.scalarFit hd) M.extent)
    (by have Hs : 8256 ≤ size := M.saved; change 8248 ≤ size; omega) (M.scalarFit hd)
    (.inr (by change 8248 ≤ d; omega))

theorem StageFrame.mask_keep {base : Addr} {s t : State} {output len : Nat}
    (F : StageFrame base s t output len) (ho : r ≤ output) :
    flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s := by
  have lo : 14720 ≤ output := ho
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem base (Layout.field .mask) 1 = val32 s.mem base (Layout.field .mask) 1 := by
    apply F.mem.val32
    · intro pair hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · change 8248 ≤ 0 ∨ 7048 ≤ 8244
        omega
      · change 8248 ≤ output ∨ output + len ≤ 8244
        omega
    · decide
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.Dsa.X86
