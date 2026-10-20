module

public import VerifiedGarbage.Proof.Rc2.X86_64.Lit
meta import VerifiedGarbage.Proof.Rc2.X86_64.Lit
public import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
meta import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # Literal CBC callers -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.X86_64.Cbc.encrypt
materialize_code Impl.Rc2.X86_64.Cbc.decrypt

end VG
