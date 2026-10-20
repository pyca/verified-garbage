module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall

/-! Public table construction reuses the existing 176-byte shared-call reservation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm

theorem combPrecompute_stack (b : MontBackend) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.CombPrecompute.code
      (MontCall.op b.name b.mul) VG.Proof.Ffdh.Arm.VettedBound.code)≤176 := by
  have bound := b.stackOk
  have zero0 : FrameStack.armStack PublicFn.prepare=0 := rfl
  have zero1 : FrameStack.armStack importModulus=0 := rfl
  have zero2 : FrameStack.armStack precomputeInverse=0 := rfl
  have zero3 : FrameStack.armStack NormalizedR2.init=0 := rfl
  have zero4 : FrameStack.armStack doubleLoop=0 := rfl
  have zero5 : FrameStack.armStack VG.Proof.Ffdh.Arm.VettedBound.code=0 := rfl
  have zero6 : FrameStack.armStack VG.Impl.Ffdh.Arm.CombPrecompute.metadata=0 := rfl
  have zero7 : FrameStack.armStack VG.Impl.Ffdh.Arm.CombPrecompute.montgomeryOut=0 := rfl
  have zero8 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.importAt 1 56 32)=0 := rfl
  have zero9 : FrameStack.armStack (smallConst 7 1)=0 := rfl
  have zero10 : ∀ o, FrameStack.armStack (VG.Impl.Ffdh.Arm.CombPrecompute.store o)=0 := by intro o; rfl
  have zero11 : FrameStack.armStack VG.Impl.Ffdh.Arm.CombPrecompute.productLoad=0 := rfl
  have zero12 : FrameStack.armStack VG.Impl.Ffdh.Arm.CombPrecompute.productStore=0 := rfl
  simp only [VG.Impl.Ffdh.Arm.CombPrecompute.code,VG.Impl.Ffdh.Arm.CombPrecompute.main,
    VG.Impl.Ffdh.Arm.CombPrecompute.table,VG.Impl.Ffdh.Arm.CombPrecompute.initial,
    VG.Impl.Ffdh.Arm.CombPrecompute.basis,VG.Impl.Ffdh.Arm.CombPrecompute.squares,
    VG.Impl.Ffdh.Arm.CombPrecompute.products,VG.Impl.Ffdh.Arm.framed,VG.Impl.Ffdh.Arm.Domain.ret,
    VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt,VG.Impl.Ffdh.Arm.NormalizedPrepare.code,
    NormalizedPrecompute.precompute,NormalizedR2.r2,SharedR2.squares,SharedWindow.init,
    MontCall.op,FrameStack.armStack,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul,
    Nat.max_self,Nat.max_zero,Nat.zero_max,zero0,zero1,zero2,zero3,zero4,zero5,zero6,
    zero7,zero8,zero9,zero10,zero11,zero12]
  omega

end VG.Proof.Ffdh.Arm
