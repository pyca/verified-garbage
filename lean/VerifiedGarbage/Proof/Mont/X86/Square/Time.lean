module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
meta import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified

@[expose] public section
namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Proof.Mont.X86.Rt

theorem constantTime :
    ConstantTime isa (Spec.Rsa.MontMul.mulContract abi 0).pre (Spec.Rsa.MontMul.mulContract abi 0).pub Impl.Mont.X86.Rt.Square.dispatch :=
  VG.Taint.constantTime (A := sseTaint) rtTaint (fun _ _ h1 h2 hp =>
    rtTaint_agree (rtAbi_of h1) (rtAbi_of h2) (rt_publicArgs hp).1 (rt_publicArgs hp).2) (by taint_decide)

end VG.Proof.Mont.X86.Square
