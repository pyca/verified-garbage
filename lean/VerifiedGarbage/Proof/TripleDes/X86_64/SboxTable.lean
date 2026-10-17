module

public import VerifiedGarbage.Impl.TripleDes.X86_64.Sbox
meta import VerifiedGarbage.Impl.TripleDes.X86_64.Sbox
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
The code of the eight S-boxes (written out in `Impl`) as one table
(`materialize_table`), which the literals of the code that runs them read.
-/

@[expose] public section

namespace VG

materialize_table Impl.TripleDes.X86_64.sboxCode 8

end VG
