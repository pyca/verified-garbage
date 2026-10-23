module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipelineOp
public import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic

/-! The shared integrated scan, unrolled at the common widths (`FiosFast`), supplies the CRT
window; other rows retain UMAAL. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.CrtFios

def phase : VG.Prog VG.Arm.isa := SharedWindow.phase (MontPipeline.op FiosFast.round)
def code : VG.Prog VG.Arm.isa := umaalArithmetic (CrtFn.codeWith phase)

end VG.Impl.Bignum.Arm.CrtFios
