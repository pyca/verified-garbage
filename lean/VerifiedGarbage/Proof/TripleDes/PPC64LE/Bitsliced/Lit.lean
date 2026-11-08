module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.SboxLit
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.Bitsliced
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! The bitsliced ECB functions' code as literals. -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.PPC64LE.Bitslice.encrypt
materialize_code Impl.TripleDes.PPC64LE.Bitslice.decrypt

end VG
