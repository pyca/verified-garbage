module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! Scalar cutting with a supplied public-bound computation. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.SampleScalar
open VG VG.Arm VG.Impl.Ffdh.Arm.Domain

def code (bound : Prog isa) : Prog isa := .seq bound
  (.seq (.block GenerateKey.scalarArgs) (.seq GenerateKey.cutEntropy (.block [.ldrSp .r0 0])))

end VG.Impl.Ffdh.Arm.SampleScalar
