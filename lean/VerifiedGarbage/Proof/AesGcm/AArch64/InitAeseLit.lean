module

public import VerifiedGarbage.Impl.AesGcm.AArch64.InitAese
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.AesGcm.AArch64.InitAese
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# AES-GCM key setup with the AES instructions on AArch64, as a literal

`vg_aes_gcm_init`'s leaf code for CPUs with FEAT_AES, built by functions, as
a literal (`materialize_code`): the checks that evaluate it (`lit_decide`,
`taint_decide`, the registration file's `spSafe`) read the literal instead of
building the code again.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.InitAese
materialize_code init
end VG.Impl.AesGcm.AArch64.InitAese
