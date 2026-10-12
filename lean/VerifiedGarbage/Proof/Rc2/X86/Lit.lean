module

public import VerifiedGarbage.Impl.Rc2.X86.Block
meta import VerifiedGarbage.Impl.Rc2.X86.Block
public import VerifiedGarbage.Proof.Rc2.X86.KeyLit
meta import VerifiedGarbage.Proof.Rc2.X86.KeyLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Impl.Rc2.X86

materialize_value keyLookup

materialize_flat_code encryptBlock
materialize_flat_code decryptBlock

end VG.Impl.Rc2.X86
