import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceAvx2.decrypt

end VG
