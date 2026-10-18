module

public import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit
public import VerifiedGarbage.Impl.Sm4.X86.Ecb
meta import VerifiedGarbage.Impl.Sm4.X86.Ecb
public import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.X86.ExpandKey
public import VerifiedGarbage.Impl.Sm4.X86.Prepared
meta import VerifiedGarbage.Impl.Sm4.X86.Prepared
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# SM4 on x86 (32-bit): the code as literals

The code of the key expansion, of ECB in both directions, and of the
preparation of the round keys and a batch under them as literals
(`materialize_flat_code`, `Proof/Framework/Lit.lean`), which the checks of
the whole functions (`taint_decide`, `lit_decide`) read rather than build
the code again in each of them.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

materialize_flat_code expandKeyCode := Impl.Sm4.X86.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.X86.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.X86.ecb .decrypt
materialize_flat_code prepareKeysCode := Impl.Sm4.X86.prepareKeys
materialize_flat_code cryptPreparedCode := Impl.Sm4.X86.cryptPrepared

end VG.Proof.Sm4.X86
