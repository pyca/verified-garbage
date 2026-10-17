module

public import VerifiedGarbage.Proof.Rc2.X86_64.Lit
meta import VerifiedGarbage.Proof.Rc2.X86_64.Lit
public import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
meta import VerifiedGarbage.Impl.Rc2.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! # Literal CBC callers -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.X86_64.Cbc.encrypt
materialize_code Impl.Rc2.X86_64.Cbc.decrypt

end VG
