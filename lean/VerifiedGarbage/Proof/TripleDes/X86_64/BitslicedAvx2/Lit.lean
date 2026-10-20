module

import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx2
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.BitslicedAvx2
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.decrypt

end VG
