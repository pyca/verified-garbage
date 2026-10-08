import VerifiedGarbage.Impl.Blowfish.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Lit

namespace VG

materialize_code Impl.Blowfish.AArch64.encrypt
materialize_code Impl.Blowfish.AArch64.decrypt
materialize_code Impl.Blowfish.AArch64.expandKey

end VG
