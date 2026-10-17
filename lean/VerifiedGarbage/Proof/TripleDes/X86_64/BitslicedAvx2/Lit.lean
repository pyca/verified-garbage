module

public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.decrypt

end VG
