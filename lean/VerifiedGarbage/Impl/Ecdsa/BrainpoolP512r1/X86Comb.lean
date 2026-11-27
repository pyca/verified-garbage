module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86
public import VerifiedGarbage.Impl.BrainpoolP512r1.CombTable7

/-! # brainpoolP512r1's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def brainpoolp512r1d : CombData := ⟨7, Impl.BrainpoolP512r1.comb7, Impl.BrainpoolP512r1.comb7Start, "VG_BRAINPOOLP512R1_COMB", false⟩

def brainpoolp512r1Comb : Cfg := { brainpoolp512r1 with comb := some brainpoolp512r1d }

/-- `vg_ecdsa_brainpoolp512r1_sign_k`. -/
def signBrainpoolP512r1Comb : Prog isa := brainpoolp512r1Comb.signComb

end VG.Impl.Ecdsa.X86
