import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Ed25519.X86.Verify
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
materialize_code pointEqualFirst := (.block (fieldCode pointEqualOps ++ fieldEqual 8 9) : Prog isa)
materialize_code pointEqualSecond := (.block (fieldEqual 10 11) : Prog isa)
materialize_code verifyFinishBlock := (.block verifyFinish : Prog isa)
materialize_code verifyReadA := (.block (pointTableRead 7680) : Prog isa)
materialize_code verifyScalarTail := (.block (copyWords 64 8 ++ scalarSubtract ++ ([.alu .test .ebx (.reg .ebx)] : List Instr)) : Prog isa)
materialize_code verifyLoadWords := (.block (copyWords 96 8) : Prog isa)
materialize_code doubleWindow
materialize_code windowPrep
end VG.Proof.Ed25519.X86
