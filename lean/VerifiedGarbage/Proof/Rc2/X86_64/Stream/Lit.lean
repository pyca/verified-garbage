module

public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
meta import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
public import VerifiedGarbage.Impl.Rc2.X86_64.Stream
meta import VerifiedGarbage.Impl.Rc2.X86_64.Stream
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Literal streaming functions -/

@[expose] public section

namespace VG

materialize_code Impl.Rc2.X86_64.Stream.init
materialize_code Impl.Rc2.X86_64.Stream.encryptUpdate
materialize_code Impl.Rc2.X86_64.Stream.decryptUpdate

end VG
