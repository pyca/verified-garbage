module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Reading the public q-workspace link reveals no key material -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_qSource_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (.block CrtFn.qSource) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (.block [.ldrSp .r1 8]) (fun _ _ => True) :=
    (loadStack_ct .r1 8).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have wp (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa (.block [.ldrSp .r1 8]) s (fun t => t.gpr .r1 = g.base) := by
    refine wp_loadStack (a := VG.Proof.Mont.off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.stack.nowrap; omega)) (h.stack.read (by decide)) fun t a => WP.block_nil ?_
    exact a.gpr.trans h.savedMain
  have first := load.wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have second : RelCT isa (fun s t => True ∧ s.gpr .r1 = g.base ∧ t.gpr .r1 = g.base)
      (.block [.ldr .r1 .r1 228]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.trans h.2.2.symm
  exact RelCT.block_append (M := isa) (l₁ := [.ldrSp .r1 8]) (l₂ := [.ldr .r1 .r1 228]) (first.seq second)

end VG.Proof.Bignum.Arm
