module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.AArch64.BitsliceNeon.encrypt
materialize_code Impl.TripleDes.AArch64.BitsliceNeon.decrypt

end VG
