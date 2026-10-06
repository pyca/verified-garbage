import VerifiedGarbage.Impl.Ecdsa.AArch64
import VerifiedGarbage.Spec.P256
import VerifiedGarbage.Impl.P256.CombTable7

/-! # ECDSA over P-256 on AArch64: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-256 as the code has it. -/
def p256 : Cfg := ⟨4, Spec.P256.curve, Impl.P256.p256Comb7, Impl.P256.p256Comb7Start, "VG_P256_COMB", true⟩

/-- `vg_ecdsa_p256_sign`. -/
def signP256 : Prog isa := p256.sign

end VG.Impl.Ecdsa.AArch64
