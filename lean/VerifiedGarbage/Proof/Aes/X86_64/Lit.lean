module

public import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
meta import VerifiedGarbage.Impl.Aes.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Aes.X86_64.AesNi
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Aes.X86_64.AesNi
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

/-!
# The AES key expansions on x86-64, as literals

The code of `vg_aes_expand_key_scratch` and `vg_aes_expand_key_scratch_aesni`,
built by functions, as literals (`materialize_code`): the checks that evaluate
it (`lit_decide`, `taint_decide`, here and in the modes that call it) read the
literal instead of building the code again.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64
materialize_code expandKey
end VG.Impl.Aes.X86_64

namespace VG.Impl.Aes.X86_64.AesNi
materialize_code expandKey
end VG.Impl.Aes.X86_64.AesNi
