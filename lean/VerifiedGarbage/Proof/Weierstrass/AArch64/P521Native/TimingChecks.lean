module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.TimingDomain
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.TimingDomain
public meta import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public meta import VerifiedGarbage.TCB.AArch64.Isa

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

deriving instance Lean.ToExpr for VReg
deriving instance Lean.ToExpr for Prod

theorem prepare_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])) validateAndPrepare :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem recode_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x5])) recodeScalar :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x19,.x5])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem build_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x26,.x20])) buildTable :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x26,.x20])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem normalize_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x26])) normalizeAndInit :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x26])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem window_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26])) windowLoop :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x19,.x26])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem finish_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20])) finishAndWrite :=
  P521NativeTiming.constantTime (AArch64.Taint.ofRegs [.x0,.x19,.x26,.x20])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Weierstrass.AArch64.P521Native
