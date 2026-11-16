module

public import VerifiedGarbage.Impl.CmacAes.X86_64.Keyed
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.CmacAes.X86_64.Keyed
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# AES-CMAC on x86-64: the code of `vg_cmac_aes_update` with keys once, as literals

`vg_aes_ctr32_keys`, `vg_aes_ctr32_keyed` and the `vg_cmac_aes_update` that
calls them (`Impl/CmacAes/X86_64/Keyed.lean`), as literals
(`materialize_code`), which the checks that evaluate them read.
-/

@[expose] public section

namespace VG.Impl.CmacAes.X86_64
materialize_code keys
materialize_code ctr32K
materialize_code updateK
end VG.Impl.CmacAes.X86_64
