module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Sbox
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
The code of the eight S-boxes (written out in `Impl`) as one table
(`materialize_table`), which the literals of the code that runs them read.
-/

@[expose] public section

namespace VG

materialize_table Impl.TripleDes.AArch64.sboxCode 8

end VG
