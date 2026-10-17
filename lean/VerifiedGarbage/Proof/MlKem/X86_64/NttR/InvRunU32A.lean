module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunU321
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.InvRunU321
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, pass A after reading `u32`s

The state after pass A, as a literal, from that after pass B, and the
check of its output (`checkI_u32`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stIU32A

theorem checkI_u32 : checkI .u32 passIBsU32 = true :=
  checkI_of (p₀ := passIBU320) (p₁ := passIBU321) (show stIU32A.any outOk = true by rw [stIU32A.lit_eq]; lit_decide)

end VG.Proof.MlKem.X86_64.NttR
