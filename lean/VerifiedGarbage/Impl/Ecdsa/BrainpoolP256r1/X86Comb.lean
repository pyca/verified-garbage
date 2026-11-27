module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86
public import VerifiedGarbage.Impl.BrainpoolP256r1.CombTable7

/-! # brainpoolP256r1's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def brainpoolp256r1d : CombData := ⟨7, Impl.BrainpoolP256r1.comb7, Impl.BrainpoolP256r1.comb7Start, "VG_BRAINPOOLP256R1_COMB", false⟩

def brainpoolp256r1Comb : Cfg := { brainpoolp256r1 with comb := some brainpoolp256r1d }

/-- `vg_ecdsa_brainpoolp256r1_sign_k`. -/
def signBrainpoolP256r1Comb : Prog isa := brainpoolp256r1Comb.signComb

end VG.Impl.Ecdsa.X86
