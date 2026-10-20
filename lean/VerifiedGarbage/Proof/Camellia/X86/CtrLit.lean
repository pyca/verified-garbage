module

public import VerifiedGarbage.Impl.Camellia.X86.Ctr
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.X86.Ctr
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # Camellia-CTR on x86: code literals for the whole-function checks -/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code ctrCode := Impl.Camellia.X86.ctr

end VG.Proof.Camellia.X86
