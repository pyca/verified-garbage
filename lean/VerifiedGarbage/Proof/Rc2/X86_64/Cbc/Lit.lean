module

public import VerifiedGarbage.Proof.Rc2.X86_64.Lit
public import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Rc2.X86_64.Lit
meta import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Literal CBC callers -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.X86_64.Cbc.encrypt
materialize_code Impl.Rc2.X86_64.Cbc.decrypt

end VG
