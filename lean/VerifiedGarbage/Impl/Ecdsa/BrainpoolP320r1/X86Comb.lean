module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86
public import VerifiedGarbage.Impl.BrainpoolP320r1.CombTable7

/-! # brainpoolP320r1's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def brainpoolp320r1d : CombData := ⟨7, Impl.BrainpoolP320r1.comb7, Impl.BrainpoolP320r1.comb7Start, "VG_BRAINPOOLP320R1_COMB", false⟩

def brainpoolp320r1Comb : Cfg := { brainpoolp320r1 with comb := some brainpoolp320r1d }

/-- `vg_ecdsa_brainpoolp320r1_sign_k`. -/
def signBrainpoolP320r1Comb : Prog isa := brainpoolp320r1Comb.signComb

end VG.Impl.Ecdsa.X86
