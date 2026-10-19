module

public import VerifiedGarbage.Proof.Dsa.AArch64.JointCallCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands

/-! # Joint-call timing in the persistent verification workspace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ReadyProductPublic.joint {d : Nat} (p : ReadyProductPublic .p d) (a b : Operand) : JointCallPublic :=
  { p.call a b with
    qLen := p.layout.qLen
    qPositive := p.layout.widths.1
    qBound := by have := p.layout.widths; omega
    parentSpace := by change 344 ≤ pWorkspace; decide }

theorem readyJoint_ct (M : Mont) (d : Nat) (a b : Operand)
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (hpa : stablePointer a.pointer) (hpb : stablePointer b.pointer)
    (hd : d < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a b (Core.element d) pWorkspace)) hc).isSome = true) :
    RelCT isa (Two fun p : ReadyProductPublic .p d => ReadyCallPre .p d a b p.toReadyCallPublic)
      (Core.joint M.mm pWorkspace a b (Core.element d)) (fun _ _ => True) := by
  apply two_map (fun p : ReadyProductPublic .p d => p.joint a b) ?_ (coreJoint_ct M (output := Core.element d) (o := pWorkspace) ha hb hd hT)
  intro p s h
  obtain ⟨eb, he, hL⟩ := h.1.availableLocal .q u (by decide) (by have := p.layout.widths; change u + p.layout.qLen ≤ usedBytes; unfold u usedBytes; omega)
  obtain ⟨fb, hf, hF⟩ := h.1.availableLocal .q v (by decide) (by have := p.layout.widths; change v + p.layout.qLen ≤ usedBytes; unfold v usedBytes; omega)
  refine ⟨readyCall_pre hpa hpb h, rfl, eb, fb, he.source, hf.source, hL, hF, ?_⟩
  exact h.1.length .q

end VG.Proof.Dsa.AArch64
