module

public import VerifiedGarbage.Impl.Blowfish.RISCV64.Modes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.RISCV64.Modes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Blowfish's modes on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.RISCV64.cbcEncryptChained
materialize_code Impl.Blowfish.RISCV64.cbcDecryptChained
materialize_code Impl.Blowfish.RISCV64.ofb
materialize_code Impl.Blowfish.RISCV64.cfbEncrypt
materialize_code Impl.Blowfish.RISCV64.cfbDecrypt

end VG
