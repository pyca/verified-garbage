import VerifiedGarbage.Impl.Seed.AArch64.Ecb
import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The code as literals, for the checks that evaluate it -/

namespace VG.Impl.Seed.AArch64

materialize_value g16
materialize_code encrypt
materialize_code decrypt
materialize_code expandKey

end VG.Impl.Seed.AArch64
