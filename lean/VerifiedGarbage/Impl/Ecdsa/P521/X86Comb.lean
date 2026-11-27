module

public import VerifiedGarbage.Impl.Ecdsa.P521.X86
public import VerifiedGarbage.Impl.P521.CombTable7

/-! # P-521's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def p521d : CombData := ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false⟩

def p521Comb : Cfg := { p521 with comb := some p521d }

/-- `vg_ecdsa_p521_sign_k`. -/
def signP521Comb : Prog isa := p521Comb.signComb

end VG.Impl.Ecdsa.X86
