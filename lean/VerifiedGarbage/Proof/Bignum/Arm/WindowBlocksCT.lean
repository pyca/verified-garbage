module

import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The control blocks of the windowed exponentiation leak only the workspace pointer

Each block's addresses are the workspace pointer `r0` plus constants. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Two runs of `a` then `b` from states each satisfying its own
precondition, with the same stack pointer. -/
theorem relCT_chain {P₁ P₂ Q₁ Q₂ : State → Prop} {a b : Prog isa}
    (ha : RelCT isa (fun s t => P₁ s ∧ P₂ t ∧ s.sp = t.sp) a (fun _ _ => True))
    (wa₁ : ∀ s, P₁ s → WP isa a s Q₁) (wa₂ : ∀ s, P₂ s → WP isa a s Q₂)
    (hb : RelCT isa (fun s t => Q₁ s ∧ Q₂ t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P₁ s ∧ P₂ t ∧ s.sp = t.sp) (.seq a b) (fun _ _ => True) :=
  ((relCT_keep_sp ha (fun _ _ h => h.2.2)).wp (fun s t h => ⟨wa₁ s h.1, wa₂ t h.2.1⟩)).seq
    (hb.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

theorem r0_agree {s t : State} (h : s.gpr .r0 = t.gpr .r0) : taint.Agree (Taint.ofRegs [.r0]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

theorem tableInit_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block tableInit) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem entryNext_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block entryNext) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem entryCopyArgs_ct (a : Nat) (ha : a < 8) :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block (entryCopyArgs a)) (fun _ _ => True) := by
  have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem scanHead_ct :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block (scanBit ++ scanArgs)) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem windowReset_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block windowReset) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem windowBitValue_ct :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block windowBitValue) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem setBit_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block [.mov .r11 (.imm 1)])
    (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem expShift_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block expShift) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem expDecrement_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block expDecrement) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

theorem expByteNext_ct : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block expByteNext) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun _ _ h => r0_agree h) (by taint_decide)

end VG.Proof.Bignum.Arm
