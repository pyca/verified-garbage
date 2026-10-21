module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
public import VerifiedGarbage.Proof.Dsa.X86.DispatchTiming

/-! # Constant-time dispatch over the public generation widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveDispatch_relCT (widths : List (Nat × Nat)) (pLen qLen : Nat)
    (base : Addr) (size : Nat) (R Q : State → State → Prop)
    (I : CompareInvariant base size R) (hz : Layout.saved ≤ size)
    (member : (pLen, qLen) ∈ widths) (bound : ∀ w ∈ widths, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32)
    (P : ∀ s t, R s t → (pointerValue base s (.input .pLen)).toNat = pLen ∧
      (pointerValue base t (.input .pLen)).toNat = pLen)
    (Qlen : ∀ s t, R s t → (pointerValue base s (.input .qLen)).toNat = qLen ∧
      (pointerValue base t (.input .qLen)).toNat = qLen)
    (body : RelCT isa R (Generate.deriveSized pLen qLen) Q) :
    RelCT isa R (Generate.deriveDispatch widths) Q :=
  generationDispatch_relCT Generate.deriveSized widths pLen qLen base size R Q I hz member bound P Qlen body

end VG.Proof.Dsa.X86
