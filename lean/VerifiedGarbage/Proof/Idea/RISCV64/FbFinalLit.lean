module

public import VerifiedGarbage.Impl.Idea.RISCV64.FbFinal
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Idea.RISCV64.FbFinal
meta import VerifiedGarbage.Proof.Idea.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # IDEA's final CFB and OFB functions on RISC-V, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.RISCV64.cfbEncryptFinal
materialize_code Impl.Idea.RISCV64.cfbDecryptFinal
materialize_code Impl.Idea.RISCV64.ofbFinal

end VG
