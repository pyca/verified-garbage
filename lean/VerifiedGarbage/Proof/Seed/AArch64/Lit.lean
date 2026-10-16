module

import VerifiedGarbage.Impl.Seed.AArch64.Ecb
meta import VerifiedGarbage.Impl.Seed.AArch64.Ecb
public import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
meta import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The code as literals, for the checks that evaluate it -/

@[expose] public section

namespace VG.Impl.Seed.AArch64

materialize_value g16
materialize_code encrypt
materialize_code decrypt
materialize_code expandKey

end VG.Impl.Seed.AArch64
