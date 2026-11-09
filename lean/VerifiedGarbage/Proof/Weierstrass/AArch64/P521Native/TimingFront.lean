module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.TimingChecks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeFront
public meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.TimingChecks
public meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeFront
public meta import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

theorem native_front_constantTime :
    ConstantTime isa (fun _ => True)
      (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])) nativeFront :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Weierstrass.AArch64.P521Native
