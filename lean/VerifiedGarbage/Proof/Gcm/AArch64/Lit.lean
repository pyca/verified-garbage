module

public import VerifiedGarbage.Impl.Gcm.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Gcm.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # GHASH on AArch64: the code as a literal, for the checks that evaluate it -/

@[expose] public section

namespace VG.Impl.Gcm.AArch64
materialize_code ghash
materialize_code keyPowers
end VG.Impl.Gcm.AArch64
