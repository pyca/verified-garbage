module

import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.AArch64.BitsliceNeon.encrypt
materialize_code Impl.TripleDes.AArch64.BitsliceNeon.decrypt

end VG
