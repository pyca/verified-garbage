module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive

/-! One public-value derivation program for every shared Montgomery backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def code (b : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.SharedDerive.code (MontCall.op b.name b.mul)

theorem stack_ok (b : MontBackend) : FrameStack.armStack (code b) ≤ 176 := by
  have bound := b.stackOk
  have s0 : FrameStack.armStack PublicFn.prepare = 0 := by rfl
  have s1 : FrameStack.armStack importModulus = 0 := by rfl
  have s2 : FrameStack.armStack precomputeInverse = 0 := by rfl
  have s3 : FrameStack.armStack NormalizedR2.init = 0 := by rfl
  have s4 : FrameStack.armStack doubleLoop = 0 := by rfl
  have s5 : FrameStack.armStack (smallConst 7 1) = 0 := by rfl
  have s6 : FrameStack.armStack SharedWindow.tablePrepare = 0 := by rfl
  have s7 : FrameStack.armStack (entryCopy 1) = 0 := by rfl
  have s8 : FrameStack.armStack scan = 0 := by rfl
  have s9 : FrameStack.armStack expByteHead = 0 := by rfl
  have s10 : FrameStack.armStack VG.Impl.Ffdh.Arm.SharedExchange.finish = 0 := by rfl
  have s11 : FrameStack.armStack (VG.Impl.Ffdh.Arm.inRange 6) = 0 := by rfl
  have s12 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) = 0 := by rfl
  have s13 : FrameStack.armStack VG.Impl.Ffdh.Arm.powerImport = 0 := by rfl
  have s14 : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange = 0 := by rfl
  have s15 : FrameStack.armStack VG.Impl.Ffdh.Arm.SharedDerive.fail = 0 := by rfl
  simp only [code, VG.Impl.Ffdh.Arm.SharedDerive.code,
    VG.Impl.Ffdh.Arm.SharedDerive.main, VG.Impl.Ffdh.Arm.SharedDerive.tail,
    VG.Impl.Ffdh.Arm.SharedCheckPublic.powerAt,
    VG.Impl.Ffdh.Arm.framed, VG.Impl.Ffdh.Arm.Domain.head, VG.Impl.Ffdh.Arm.Domain.ifFlag,
    VG.Impl.Ffdh.Arm.Domain.testFlag, VG.Impl.Ffdh.Arm.Domain.ret,
    VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt,
    VG.Impl.Ffdh.Arm.NormalizedPrepare.code, NormalizedPrecompute.precompute, NormalizedR2.r2, SharedR2.squares,
    SharedWindow.phase, SharedWindow.init, SharedWindow.tableBuild,
    SharedWindow.tableBody, SharedWindow.bytes, SharedWindow.bits,
    SharedWindow.round, SharedWindow.bit, SharedWindow.apply,
    MontCall.op, FrameStack.armStack, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.max_self, Nat.max_zero, Nat.zero_max,
    s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]
  omega

end VG.Proof.Ffdh.Arm.SharedDerive
