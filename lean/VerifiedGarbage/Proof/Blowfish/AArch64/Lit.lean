module

public import VerifiedGarbage.Impl.Blowfish.AArch64
meta import VerifiedGarbage.Impl.Blowfish.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.AArch64.encrypt
materialize_code Impl.Blowfish.AArch64.decrypt
materialize_code Impl.Blowfish.AArch64.expandKey

end VG
