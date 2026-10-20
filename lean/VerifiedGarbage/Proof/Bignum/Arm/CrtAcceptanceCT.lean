module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtAcceptance

import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtAcceptance
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Installing a secret acceptance bit has public memory addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_installAcceptance_ct : RelCT isa
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp) (.block installAcceptance) (fun _ _ => True) := by
  have addr : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
      (.block [.addSp .r12 48])
      (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12) := by
    apply single_ct (fun _ _ _ => rfl)
    intro s t u v h e1 e2
    simp only [exec, Nat.reduceLT, ite_true, Option.some.injEq] at e1 e2
    subst u; subst v
    simp only [State.setReg, ite_true, h.1, h.2]
    exact ⟨trivial, trivial⟩
  have store : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12)
      (.block [.ldr .r11 .r12 0, .str .r11 .r0 212]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2
  exact RelCT.block_append (M := isa) (l₁ := [.addSp .r12 48])
    (l₂ := [.ldr .r11 .r12 0, .str .r11 .r0 212]) (addr.seq store)

end VG.Proof.Bignum.Arm
