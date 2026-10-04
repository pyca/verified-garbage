import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Lit

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceSse.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceSse.decrypt

end VG
