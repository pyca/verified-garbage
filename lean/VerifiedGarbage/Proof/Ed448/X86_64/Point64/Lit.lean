module

import VerifiedGarbage.Proof.X448.X86_64.Lit
public import VerifiedGarbage.Impl.Ed448.X86_64.Point64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Impl.Ed448.X86_64.Point64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! The point functions' code as literals (`materialize_code`), which their checks, and those
of the code that calls them, read rather than build each field multiplication again. -/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.Point64.doubleFn
materialize_code Impl.Ed448.X86_64.Point64.addFn

end VG
