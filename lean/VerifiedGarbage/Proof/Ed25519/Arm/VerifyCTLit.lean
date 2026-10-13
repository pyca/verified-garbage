module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.Ed25519.Arm.Verify
meta import VerifiedGarbage.Impl.Ed25519.Arm.Verify
public import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
