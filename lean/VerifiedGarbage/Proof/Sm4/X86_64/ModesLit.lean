module

public import VerifiedGarbage.Proof.Sm4.X86_64.Lit
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
public import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
meta import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
public import VerifiedGarbage.Impl.Sm4.X86_64.Fb
meta import VerifiedGarbage.Impl.Sm4.X86_64.Fb
public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
meta import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# SM4's modes on x86-64: the code as literals

As `Lit.lean`, for CBC, CTR, OFB and CFB128, whose code the checks of the
whole functions (`taint_decide`, `lit_decide`: the ABI, the stack scratch
and `spSafe`) evaluate several times each.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

materialize_flat_code cbcEncryptCode := Impl.Sm4.X86_64.cbcEncrypt
materialize_flat_code cbcDecryptCode := Impl.Sm4.X86_64.cbcDecrypt
materialize_flat_code ctrCode := Impl.Sm4.X86_64.ctr
materialize_flat_code ofbCode := Impl.Sm4.X86_64.ofb
materialize_flat_code cfbEncryptCode := Impl.Sm4.X86_64.cfbEncrypt
materialize_flat_code cfbDecryptCode := Impl.Sm4.X86_64.cfbDecrypt

end VG.Proof.Sm4.X86_64
