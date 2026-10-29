module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
-- `roundConsts`'s literal: `FunctionsLit` imports it privately, and without it
-- the kernel rebuilds the round's constants in each mode (seconds each).
import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.RISCV64.Modes
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Triple DES's modes on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.RISCV64.cbcEncryptChained
materialize_code Impl.TripleDes.RISCV64.cbcDecryptChained
materialize_code Impl.TripleDes.RISCV64.ofb
materialize_code Impl.TripleDes.RISCV64.cfbEncrypt
materialize_code Impl.TripleDes.RISCV64.cfbDecrypt
materialize_code Impl.TripleDes.RISCV64.cfb8Encrypt
materialize_code Impl.TripleDes.RISCV64.cfb8Decrypt

end VG
