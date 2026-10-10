import VerifiedGarbage.Impl.TripleDes.Arm.Sbox
import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
The code of the eight S-boxes (written out in `Impl`) as one table
(`materialize_table`), which the literals of the code that runs them read.
-/

namespace VG

materialize_table Impl.TripleDes.Arm.sboxCode 8

end VG
