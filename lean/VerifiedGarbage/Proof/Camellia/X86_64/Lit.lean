module

public import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
meta import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
public import VerifiedGarbage.Impl.Camellia.X86_64.Prepared
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Camellia.X86_64.Prepared
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Spec.Camellia.Contract
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# Camellia on X86_64: the code as literals

The code of the key expansion, of ECB in both directions and of the
batches under prepared subkeys as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again (seconds for the key expansion's).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

materialize_flat_code expandKeyCode := Impl.Camellia.X86_64.expandKey
materialize_flat_code ecbEncrypt := Impl.Camellia.X86_64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Camellia.X86_64.ecb .decrypt
materialize_flat_code cryptPreparedCode := Impl.Camellia.X86_64.cryptPrepared

end VG.Proof.Camellia.X86_64
