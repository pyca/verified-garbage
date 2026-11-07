module

public import VerifiedGarbage.Impl.Blowfish.RISCV64.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Blowfish's final CFB functions on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Blowfish.RISCV64.cfbEncryptFinal
materialize_code Impl.Blowfish.RISCV64.cfbDecryptFinal

end VG
