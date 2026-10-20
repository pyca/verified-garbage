module

public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # `vg_ghash_pclmul` on x86-64, as a literal

For the checks of every instruction and the constant-time analyses that
evaluate it. -/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.Pclmul.ghash

end VG
