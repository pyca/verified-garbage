module

import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.SboxLit
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.SboxLit
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Bitsliced
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! The bitsliced ECB functions' code as literals. -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.RISCV64.Bitslice.encrypt
materialize_code Impl.TripleDes.RISCV64.Bitslice.decrypt

end VG
