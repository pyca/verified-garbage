module

import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedSse
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceSse.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceSse.decrypt

end VG
