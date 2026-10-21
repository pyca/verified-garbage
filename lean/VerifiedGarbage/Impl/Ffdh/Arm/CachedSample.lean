module

public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar

/-! Sampling consumes public metadata without recognizing the domain again. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.CachedSample
open VG VG.Arm

def maskShift (bit amount : Nat) : Prog isa :=
  .seq (.block [.dp .and .r12 .r9 (.imm (BitVec.ofNat 32 bit)), .cmp .r12 (.imm 0)])
    (.ite .ne (.block [.mov .r3 (.shifted .r3 .lsr amount)]) (.block []))

def head : List Instr := [
  .ldrSp .r9 52, .ldr .r6 .r9 8, .ldr .r10 .r9 0,
  .dp .sub .r10 .r10 (.imm 1), .dp .and .r10 .r10 (.imm 7),
  .mov .r9 (.imm 7), .dp .sub .r9 .r9 (.reg .r10), .mov .r3 (.imm 255)]

def mask : Prog isa := .seq (maskShift 4 4) (.seq (maskShift 2 2) (maskShift 1 1))

def bound : Prog isa := .seq (.block head)
  (.seq mask (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave))

def code : Prog isa := SampleScalar.code bound

end VG.Impl.Ffdh.Arm.CachedSample
