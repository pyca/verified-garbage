module
public import VerifiedGarbage.Impl.Rsa.Arm.Div
public import VerifiedGarbage.Proof.Rsa.Arm.DivContext
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.Div
meta import VerifiedGarbage.Proof.Rsa.Arm.DivContext
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Appending the secret quotient bit has a fixed memory trace -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Bignum.Arm

theorem quotientBit_ct {g : Geometry} :
    RelCT isa (fun s t => Context g s ∧ Context g t) (.block quotientBit) (fun _ _ => True) := by
  let Q := fun s : State => s.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets 0)
  have first : RelCT isa (fun s t => Context g s ∧ Context g t)
      (.block [.ldr .r0 .r8 0]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r8]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : Context g s) : WP isa (.block [.ldr .r0 .r8 0]) s Q :=
    h.loadPtr 0 (by decide) (fun _ u _ => WP.block_nil u.gpr)
  have last : RelCT isa (fun s t => Q s ∧ Q t)
      (.block [.ldr .r3 .r0 0, .dp .eor .r11 .r11 (.imm 1),
        .dp .add .r3 .r3 (.reg .r11), .str .r3 .r0 0, .subs .r6 .r6 (.imm 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  exact ((pair_posts first wp).seq last).block_append

end VG.Proof.Rsa.Arm.Div
