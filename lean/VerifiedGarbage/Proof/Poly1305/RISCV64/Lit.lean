module

public import VerifiedGarbage.Impl.Poly1305.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Poly1305.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! Literal code, so that the kernel does not rebuild it in every check that
evaluates it (constant time, the registers written). -/

@[expose] public section

namespace VG.Impl.Poly1305.RISCV64
materialize_code init
materialize_code blocks
materialize_code update
materialize_code finalize
end VG.Impl.Poly1305.RISCV64
