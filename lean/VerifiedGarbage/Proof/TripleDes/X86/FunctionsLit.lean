module

public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
meta import VerifiedGarbage.Impl.TripleDes.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

@[expose] public section

namespace VG

/-! The functions. -/

materialize_code Impl.TripleDes.X86.encryptBlock
materialize_code Impl.TripleDes.X86.Key.expandKey
materialize_code Impl.TripleDes.X86.Ecb.encrypt
materialize_code Impl.TripleDes.X86.Ecb.decrypt

end VG
