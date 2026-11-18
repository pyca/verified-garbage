module

public import VerifiedGarbage.Impl.Ecdsa.P224.X86
public import VerifiedGarbage.Impl.P224.CombTable7

/-! # P-224's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def p224d : CombData := ⟨7, Impl.P224.p224Comb7, Impl.P224.p224Comb7Start, "VG_P224_COMB", false⟩

def p224Comb : Cfg := { p224 with comb := some p224d }

/-- `vg_ecdsa_p224_sign_k`. -/
def signP224Comb : Prog isa := p224Comb.signComb

end VG.Impl.Ecdsa.X86
