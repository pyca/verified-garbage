module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.FbFinal
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
-- `roundConsts`'s literal: `FunctionsLit` imports it privately, and without it
-- the kernel rebuilds the round's constants in each mode (seconds each).
import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # TripleDes's final CFB and OFB functions on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.RISCV64.cfbEncryptFinal
materialize_code Impl.TripleDes.RISCV64.cfbDecryptFinal
materialize_code Impl.TripleDes.RISCV64.ofbFinal

end VG
