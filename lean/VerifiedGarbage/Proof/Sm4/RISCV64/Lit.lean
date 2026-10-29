module

public import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
public import VerifiedGarbage.Impl.Sm4.RISCV64.Prepared
public import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
meta import VerifiedGarbage.Impl.Sm4.RISCV64.Prepared
meta import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# SM4 on RISCV64: the code as literals

The code of the key expansion, of ECB in both directions, and of the
preparation of the round keys and of a batch under them as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

materialize_flat_code expandKeyCode := Impl.Sm4.RISCV64.expandKey
materialize_flat_code ecbEncrypt := Impl.Sm4.RISCV64.ecb .encrypt
materialize_flat_code ecbDecrypt := Impl.Sm4.RISCV64.ecb .decrypt
materialize_flat_code prepareKeysCode := Impl.Sm4.RISCV64.prepareKeys
materialize_flat_code cryptPreparedCode := Impl.Sm4.RISCV64.cryptPrepared

end VG.Proof.Sm4.RISCV64
