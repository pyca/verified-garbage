module

public import VerifiedGarbage.Impl.Rc2.X86.Cbc
meta import VerifiedGarbage.Impl.Rc2.X86.Cbc
public import VerifiedGarbage.Proof.Rc2.X86.Lit
meta import VerifiedGarbage.Proof.Rc2.X86.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Rc2.X86.Cbc
materialize_code encrypt
materialize_code decrypt
end VG.Impl.Rc2.X86.Cbc
