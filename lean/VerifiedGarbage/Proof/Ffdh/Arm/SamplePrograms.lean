module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrograms
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailInstance
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate

/-! Sampling policies reuse the shared Montgomery key-generation program. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SampleKeyGenerate
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Bignum.Arm

def code (b : MontBackend) (sample : Prog isa) : Prog isa :=
  VG.Impl.Ffdh.Arm.SampleKeyGenerate.code (KeyGenerate.prepare b) sample (tail b)

theorem stack_ok (b : MontBackend) (sample : Prog isa)
    (sampleStack : FrameStack.armStack sample = 0) : FrameStack.armStack (code b sample) ≤ 176 := by
  have bound := b.stackOk
  have s0 : FrameStack.armStack (PublicFn.prepare) = 0 := by rfl
  have s1 : FrameStack.armStack (importModulus) = 0 := by rfl
  have s2 : FrameStack.armStack (precomputeInverse) = 0 := by rfl
  have s3 : FrameStack.armStack (NormalizedR2.init) = 0 := by rfl
  have s4 : FrameStack.armStack (doubleLoop) = 0 := by rfl
  have s5 : FrameStack.armStack (smallConst 7 1) = 0 := by rfl
  have s6 : FrameStack.armStack (smallConst 5 2) = 0 := by rfl
  have s7 : FrameStack.armStack (selectArray 6 6 1) = 0 := by rfl
  have s8 : FrameStack.armStack (VG.Impl.Bignum.Arm.TwoExp.candidate) = 0 := by rfl
  have s9 : FrameStack.armStack (SharedWindow.tablePrepare) = 0 := by rfl
  have s10 : FrameStack.armStack (entryCopy 1) = 0 := by rfl
  have s11 : FrameStack.armStack (scan) = 0 := by rfl
  have s12 : FrameStack.armStack (expByteHead) = 0 := by rfl
  have s15 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) = 0 := by rfl
  have s16 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange) = 0 := by rfl
  have s17 : FrameStack.armStack (VG.Impl.Ffdh.Arm.inRange 6) = 0 := by rfl
  have s18 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.Exchange.exportResult) = 0 := by rfl
  have s19 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.GenerateKey.finish) = 0 := by rfl
  have s20 : FrameStack.armStack (VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar) = 0 := by rfl
  have s21 : FrameStack.armStack (VG.Impl.Ffdh.Arm.powerImport) = 0 := by rfl
  have s22 : FrameStack.armStack (VG.Impl.Ffdh.Arm.detectTwo) = 0 := by rfl
  simp only [code, KeyGenerate.prepare, tail, power,
    VG.Impl.Ffdh.Arm.SampleKeyGenerate.code, VG.Impl.Ffdh.Arm.SampleKeyGenerate.main,
    VG.Impl.Ffdh.Arm.KeyGenerate.tail,
    VG.Impl.Ffdh.Arm.framed, VG.Impl.Ffdh.Arm.Domain.head,
    VG.Impl.Ffdh.Arm.Domain.ifFlag, VG.Impl.Ffdh.Arm.Domain.testFlag,
    VG.Impl.Ffdh.Arm.Domain.ret, VG.Impl.Ffdh.Arm.NormalizedPrepare.prepareAt,
    VG.Impl.Ffdh.Arm.NormalizedPrepare.code,
    NormalizedPrecompute.precompute, NormalizedR2.r2, SharedR2.squares,
    VG.Impl.Ffdh.Arm.KeyPower.powerAt, VG.Impl.Ffdh.Arm.KeyPower.power,
    VG.Impl.Ffdh.Arm.KeyPower.phase, VG.Impl.Ffdh.Arm.KeyPower.twoPhase,
    VG.Impl.Bignum.Arm.TwoExp.phase, VG.Impl.Bignum.Arm.TwoExp.initial,
    VG.Impl.Bignum.Arm.TwoExp.bytes, VG.Impl.Bignum.Arm.TwoExp.bits,
    VG.Impl.Bignum.Arm.TwoExp.round, VG.Impl.Bignum.Arm.TwoExp.bit,
    SharedWindow.phase, SharedWindow.init, SharedWindow.tableBuild,
    SharedWindow.tableBody, SharedWindow.bytes, SharedWindow.bits,
    SharedWindow.round, SharedWindow.bit, SharedWindow.apply,
    MontCall.op, FrameStack.armStack,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    Nat.max_self, Nat.max_zero, Nat.zero_max,
    sampleStack, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s15, s16, s17, s18, s19, s20, s21, s22]
  omega

end VG.Proof.Ffdh.Arm.SampleKeyGenerate
