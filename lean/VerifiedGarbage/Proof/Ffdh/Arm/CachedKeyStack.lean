module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyPrograms

/-! Cached comb attempts retain the existing 176-byte public stack reservation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedKeyGenerate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm

theorem stack_ok (backend : MontBackend) : FrameStack.armStack (code backend) ≤ 176 := by
  have prepareZero : FrameStack.armStack prepare = 0 := rfl
  have sampleZero : FrameStack.armStack sample = 0 := rfl
  have chooseZero : FrameStack.armStack CombExp.choose = 0 := rfl
  have oneZero : FrameStack.armStack (smallConst 7 1) = 0 := rfl
  have argsZero : FrameStack.armStack VG.Impl.Ffdh.Arm.CachedPower.args = 0 := rfl
  have importZero : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) = 0 := rfl
  have rangeZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange = 0 := rfl
  have publicRangeZero : FrameStack.armStack (VG.Impl.Ffdh.Arm.inRange 6) = 0 := rfl
  have exportZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult = 0 := rfl
  have finishZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish = 0 := rfl
  have failZero : FrameStack.armStack VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar = 0 := rfl
  have bound := backend.stackOk
  simp only [code, tail, VG.Impl.Ffdh.Arm.CachedKeyGenerate.code,
    VG.Impl.Ffdh.Arm.CachedKeyGenerate.body, VG.Impl.Ffdh.Arm.SampleKeyGenerate.main,
    VG.Impl.Ffdh.Arm.KeyGenerate.tail, VG.Impl.Ffdh.Arm.CachedPower.code,
    VG.Impl.Ffdh.Arm.framed, VG.Impl.Ffdh.Arm.Domain.ifFlag, VG.Impl.Ffdh.Arm.Domain.testFlag,
    CombExp.phase, CombExp.initial, CombExp.rows, CombExp.round, CombExp.step,
    MontCall.op, FrameStack.armStack, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.max_self, Nat.max_zero, Nat.zero_max,
    prepareZero, sampleZero, chooseZero, oneZero, argsZero, importZero, rangeZero,
    publicRangeZero, exportZero, finishZero, failZero]
  omega

end VG.Proof.Ffdh.Arm.CachedKeyGenerate
