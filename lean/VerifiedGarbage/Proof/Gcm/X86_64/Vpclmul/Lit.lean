module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Gcm.X86_64.Vpclmul
meta import VerifiedGarbage.Impl.Gcm.X86_64.Vpclmul

/-! # `vg_ghash_vpclmul` on x86-64, as a literal

For the checks of every instruction and the constant-time analyses that
evaluate it. -/

@[expose] public section

namespace VG

materialize_code Impl.Gcm.X86_64.Vpclmul.ghash

end VG
