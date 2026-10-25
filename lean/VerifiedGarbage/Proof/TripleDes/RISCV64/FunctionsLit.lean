module

import VerifiedGarbage.Proof.TripleDes.RISCV64.SboxTable
public import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.SboxTable
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! The functions' code as literals, and the round they share, evaluated once. -/

@[expose] public section

namespace VG

materialize_value Impl.TripleDes.RISCV64.roundBody

materialize_code Impl.TripleDes.RISCV64.Key.expandKey
materialize_code Impl.TripleDes.RISCV64.Ecb.encrypt
materialize_code Impl.TripleDes.RISCV64.Ecb.decrypt

end VG
