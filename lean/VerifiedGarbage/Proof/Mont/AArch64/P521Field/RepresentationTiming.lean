module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Representation
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Representation
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.TCB.AArch64.Isa

/-! The representation boundaries use public workspace addresses and secret field words. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

theorem representation_from_constantTime (d : Nat) :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0]))
      (.block (representationMemoryCode representationFromCode d)) := by
  have he : Code.eraseOff (.block (representationMemoryCode representationFromCode d))=
      Code.eraseOff (.block (representationMemoryCode representationFromCode 0)) := rfl
  exact VG.Taint.constantTime (A:=VG.AArch64.taint) (AArch64.Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (AArch64.Taint.isSome_check_of_eraseOff he (by taint_decide))

theorem representation_to_constantTime (d : Nat) :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0]))
      (.block (representationMemoryCode representationToCode d)) := by
  have he : Code.eraseOff (.block (representationMemoryCode representationToCode d))=
      Code.eraseOff (.block (representationMemoryCode representationToCode 0)) := rfl
  exact VG.Taint.constantTime (A:=VG.AArch64.taint) (AArch64.Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (AArch64.Taint.isSome_check_of_eraseOff he (by taint_decide))

end VG.Proof.Mont.AArch64.P521Field
