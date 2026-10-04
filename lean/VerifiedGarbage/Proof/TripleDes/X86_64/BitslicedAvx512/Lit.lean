import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.SboxLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Lit

namespace VG

materialize_code Impl.TripleDes.X86_64.BitsliceAvx512.encrypt
materialize_code Impl.TripleDes.X86_64.BitsliceAvx512.decrypt

end VG
