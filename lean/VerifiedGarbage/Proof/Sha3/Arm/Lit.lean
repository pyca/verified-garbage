module

public import VerifiedGarbage.Impl.Sha3.Arm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.Arm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# Keccak-f[1600] on ARMv7: the code as literals

The permutation's code as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`): its functions compute the rotation of every
operand, and its prologue the round constants, which the kernel would
otherwise compute in every check that evaluates the code. The blocks that
`Proof/Sha3/Arm/Round.lean` checks by evaluation are literals of their own.
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm

open VG.Arm

materialize_code permute := Impl.Sha3.Arm.permute

-- θ, ρ, π and χ of the two rounds of an iteration.
materialize_code coreA := (.block (Impl.Sha3.Arm.roundCore .r1 .r0) : Prog isa)
materialize_code coreB := (.block (Impl.Sha3.Arm.roundCore .r0 .r1) : Prog isa)

-- To and from the interleaved lanes.
materialize_code enterCode := (.block Impl.Sha3.Arm.enter : Prog isa)
materialize_code leaveCode := (.block Impl.Sha3.Arm.leave : Prog isa)

end VG.Proof.Sha3.Arm
