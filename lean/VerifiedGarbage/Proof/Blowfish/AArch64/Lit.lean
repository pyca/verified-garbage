module

public import VerifiedGarbage.Impl.Blowfish.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.AArch64.encrypt
materialize_code Impl.Blowfish.AArch64.decrypt
materialize_code Impl.Blowfish.AArch64.expandKey

end VG
