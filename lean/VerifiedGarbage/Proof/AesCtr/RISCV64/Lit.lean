module

public import VerifiedGarbage.Impl.AesCtr.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Impl.AesCtr.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-!
# AES-CTR on RISC-V, as a literal

The code of `vg_aes_ctr` as a literal (`materialize_code`), for the checks
that evaluate it (`taint_decide`).
-/

@[expose] public section

namespace VG.Impl.AesCtr.RISCV64

materialize_code crypt

end VG.Impl.AesCtr.RISCV64
