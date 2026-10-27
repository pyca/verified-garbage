module

public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
public import VerifiedGarbage.Impl.Camellia.X86.Prepared
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
meta import VerifiedGarbage.Impl.Camellia.X86.Prepared
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# Camellia on x86 (32-bit): the code as literals

The code of the key expansion and of ECB in both directions and of `vg_camellia_crypt_prepared` as literals
(`materialize_flat_code`, `Proof/Framework/Lit.lean`), which the checks of
the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

materialize_flat_code expandKeyCode := Impl.Camellia.X86.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.X86.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.X86.ecb .decrypt
materialize_flat_code cryptPreparedCode := Impl.Camellia.X86.cryptPrepared

end VG.Proof.Camellia.X86
