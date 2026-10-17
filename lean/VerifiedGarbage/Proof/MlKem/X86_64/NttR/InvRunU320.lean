module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRun
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the first half of pass B from `u32`s

The state after half 0 of pass B reading `u32`s, for `vg_mlkem_inv_ntt_avx2`, as a literal.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stIU320

end VG.Proof.MlKem.X86_64.NttR
