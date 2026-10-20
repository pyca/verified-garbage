module

public import VerifiedGarbage.Impl.Ed25519.Arm.Verify
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
public import VerifiedGarbage.Proof.Ed25519.Arm.FnLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.Arm.Verify
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.FnLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Checked code literals for verifier composition. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm
materialize_code verifyBasePoint := constPoint Spec.Ed25519.basePoint
materialize_code verifyWriteLhs := (.block (pointTableWrite 8032) : Prog isa)
materialize_code verifyReadA := (.block (pointTableRead 7776) : Prog isa)
materialize_code verifyCombine
materialize_code verifyScalarTail := (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr)) : Prog isa)
materialize_code verifySetupBlock := (.block verifySetup : Prog isa)
materialize_code verifyFinishBlock := (.block verifyFinish : Prog isa)
end VG.Proof.Ed25519.Arm
