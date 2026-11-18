module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86
public import VerifiedGarbage.Impl.BrainpoolP384r1.CombTable7

/-! # brainpoolP384r1's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def brainpoolp384r1d : CombData := ⟨7, Impl.BrainpoolP384r1.comb7, Impl.BrainpoolP384r1.comb7Start, "VG_BRAINPOOLP384R1_COMB", false⟩

def brainpoolp384r1Comb : Cfg := { brainpoolp384r1 with comb := some brainpoolp384r1d }

/-- `vg_ecdsa_brainpoolp384r1_sign_k`. -/
def signBrainpoolP384r1Comb : Prog isa := brainpoolp384r1Comb.signComb

end VG.Impl.Ecdsa.X86
