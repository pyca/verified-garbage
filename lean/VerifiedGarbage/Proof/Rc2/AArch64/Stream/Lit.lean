module

public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
public import VerifiedGarbage.Impl.Rc2.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
meta import VerifiedGarbage.Impl.Rc2.AArch64.Stream
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-! # Literal streaming RC2-CBC programs

`init` as a literal (`materialize_code`), whose call refers to the literal of
the key expansion. -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.AArch64.Stream.init

end VG
