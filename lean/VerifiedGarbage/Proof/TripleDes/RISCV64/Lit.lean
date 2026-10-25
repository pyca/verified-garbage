module

import VerifiedGarbage.Proof.TripleDes.RISCV64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Sbox
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.SboxTable
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Sbox
meta import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! The S-boxes and the fixed permutations, as literals. -/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

materialize_code initialPermutation := (.block (permuteCode Spec.TripleDes.ip 64 .t2 .t0 .t3) : Prog isa)
materialize_code finalPermutation := (.block (permuteCode Spec.TripleDes.fp 64 .t2 .t0 .t3) : Prog isa)
materialize_code keyPermutation1 := (.block (permuteCode Spec.TripleDes.pc1 64 .t2 .t0 .t3) : Prog isa)
materialize_code keyPermutation2 := (.block (permuteCode Spec.TripleDes.pc2 56 .t2 .t0 .t3) : Prog isa)

end VG.Impl.TripleDes.RISCV64
