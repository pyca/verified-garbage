module

public import VerifiedGarbage.Impl.AesCbc.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Impl.AesCbc.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-!
# AES-CBC on RISC-V, as literals

The code of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` as literals
(`materialize_code`), for the checks that evaluate it (`taint_decide`).
-/

@[expose] public section

namespace VG.Impl.AesCbc.RISCV64

materialize_code encrypt
materialize_code decrypt

end VG.Impl.AesCbc.RISCV64
