module

public import VerifiedGarbage.Impl.Seed.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.X86.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # SEED's key schedule on x86 (32-bit): the code as a literal -/

@[expose] public section

namespace VG.Proof.Seed.X86

materialize_code expandKeyCode := Impl.Seed.X86.expandKey

end VG.Proof.Seed.X86
