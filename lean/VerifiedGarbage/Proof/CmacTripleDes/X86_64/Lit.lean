module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.CmacTripleDes.X86_64
meta import VerifiedGarbage.Impl.CmacTripleDes.X86_64
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86_64.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
meta import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # TDEA-CMAC's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.X86_64.init
materialize_code Impl.CmacTripleDes.X86_64.update
materialize_code Impl.CmacTripleDes.X86_64.finalize

end VG
