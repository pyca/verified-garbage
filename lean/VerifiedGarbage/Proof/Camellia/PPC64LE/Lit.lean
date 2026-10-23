module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Prepared
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.Prepared
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-!
# Camellia on PPC64LE: the code as literals

The code of the key expansion, of ECB in both directions, and of the
preparation of the round keys and of a batch under them as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

materialize_flat_code expandKeyCode := Impl.Camellia.PPC64LE.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.PPC64LE.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.PPC64LE.ecb .decrypt
materialize_flat_code prepareKeysCode := Impl.Camellia.PPC64LE.prepareKeys
materialize_flat_code cryptPreparedCode := Impl.Camellia.PPC64LE.cryptPrepared

end VG.Proof.Camellia.PPC64LE
