module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
The code of the eight S-boxes (written out in `Impl`) as one table
(`materialize_table`), which the literals of the code that runs them read.
-/

@[expose] public section

namespace VG

materialize_table Impl.TripleDes.AArch64.sboxCode 8

end VG
