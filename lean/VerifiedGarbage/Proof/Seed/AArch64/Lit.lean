module

public import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The code as literals, for the checks that evaluate it -/

@[expose] public section

namespace VG.Impl.Seed.AArch64

materialize_value g16
materialize_code encrypt
materialize_code decrypt
materialize_code expandKey

end VG.Impl.Seed.AArch64
