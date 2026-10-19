module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Program
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The head of the forwarded additions of P-256 verification's window table, as a
literal (`Proof/Framework/Lit.lean`): `Forward.ArithmeticTableHead`'s. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

noncomputable def tableHead.lit : Prog isa := .block Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead.rightCode.lit

theorem tableHead.lit_eq :
    VerifyArithmetic.program P256Joint.cfg.K.M
      (jacHead P256Joint.cfg.K.S P256Joint.cfg.K.R (Naf.twice P256Joint.cfg.K)) = tableHead.lit :=
  (program_eq .tableHead).trans (congrArg Code.block Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead.optimized_lit)

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
