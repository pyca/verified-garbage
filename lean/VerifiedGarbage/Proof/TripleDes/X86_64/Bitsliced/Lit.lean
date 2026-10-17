module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.Bitslice.encrypt
materialize_code Impl.TripleDes.X86_64.Bitslice.decrypt

end VG
