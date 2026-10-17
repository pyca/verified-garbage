module

import VerifiedGarbage.Impl.Seed.X86_64.Ecb
meta import VerifiedGarbage.Impl.Seed.X86_64.Ecb
public import VerifiedGarbage.Impl.Seed.X86_64.ExpandKey
meta import VerifiedGarbage.Impl.Seed.X86_64.ExpandKey
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # The code as literals, for the checks that evaluate it -/

@[expose] public section

namespace VG.Impl.Seed.X86_64

materialize_value g16
materialize_code encrypt
materialize_code decrypt
materialize_code expandKey

end VG.Impl.Seed.X86_64
