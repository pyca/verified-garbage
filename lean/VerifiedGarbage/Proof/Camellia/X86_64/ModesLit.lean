module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
meta import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
public import VerifiedGarbage.Impl.Camellia.X86_64.Fb
meta import VerifiedGarbage.Impl.Camellia.X86_64.Fb
public import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
meta import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Camellia-CBC, -OFB, -CFB128 and -CTR's x86-64 code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Camellia.X86_64.cbcEncrypt
materialize_code Impl.Camellia.X86_64.cbcDecrypt
materialize_code Impl.Camellia.X86_64.ofb
materialize_code Impl.Camellia.X86_64.cfbEncrypt
materialize_code Impl.Camellia.X86_64.cfbDecrypt
materialize_code Impl.Camellia.X86_64.ctr

end VG
