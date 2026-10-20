module

public import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects

/-! # Validation preserves every operand outside the arithmetic prefix -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def stablePointer : Pointer → Prop
  | .input f => f ≠ .mask
  | _ => True

theorem Ready.pointer_eq {L : ExecutionLayout} {s t : State} (hs : Ready L s) (ht : Ready L t)
    (p : Pointer) (hp : stablePointer p) : pointerValue t.mem L.base p = pointerValue s.mem L.base p := by
  cases p with
  | input f => exact (ht.fields f hp).trans (hs.fields f hp).symm
  | «local» _ => rfl
  | signatureS =>
    exact congrArg₂ (· + ·)
      ((ht.fields .signature (by decide)).trans (hs.fields .signature (by decide)).symm)
      ((ht.fields .qLen (by decide)).trans (hs.fields .qLen (by decide)).symm)

theorem CheckEffect.preserve {L : ExecutionLayout} {s t : State} {valid : Bool}
    (h : CheckEffect L valid s t) (hs : Ready L s)
    {a : Operand} {bytes : List Byte} {Z : Nat} (hZ : activeBytes ≤ Z)
    (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (hb : OperandBytes s L.base Z a bytes) : OperandBytes t L.base Z a bytes := by
  refine ⟨(h.ready.fields a.length ha).trans ((hs.fields a.length ha).symm.trans hb.length), ?_⟩
  rw [hs.pointer_eq h.ready a.pointer hp]
  have hlo : 128 ≤ activeBytes := by decide
  exact hb.source.congrK (InScr.of_outside h.frame (by omega)) h.keep

theorem CheckEffect.scheduleFrame {L : ExecutionLayout} {s t : State} {valid : Bool}
    (h : CheckEffect L valid s t) : Outside L.base 128 (usedBytes - 128) s.mem t.mem :=
  h.frame.mono (by decide) (by decide)

end VG.Proof.Dsa.AArch64
