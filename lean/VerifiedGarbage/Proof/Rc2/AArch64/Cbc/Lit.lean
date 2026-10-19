module

public import VerifiedGarbage.Proof.Rc2.AArch64.Lit
meta import VerifiedGarbage.Proof.Rc2.AArch64.Lit
public import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
meta import VerifiedGarbage.Impl.Rc2.AArch64.Cbc
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # Literal CBC callers -/

@[expose] public section

namespace VG

materialize_flat_code Impl.Rc2.AArch64.Cbc.encrypt
materialize_flat_code Impl.Rc2.AArch64.Cbc.decrypt

end VG
