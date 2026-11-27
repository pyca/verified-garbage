module

public import VerifiedGarbage.Impl.Ecdsa.P192.X86
public import VerifiedGarbage.Impl.P192.CombTable7

/-! # P-192's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def p192d : CombData := ⟨7, Impl.P192.comb7, Impl.P192.comb7Start, "VG_P192_COMB", false⟩

def p192Comb : Cfg := { p192 with comb := some p192d }

/-- `vg_ecdsa_p192_sign_k`. -/
def signP192Comb : Prog isa := p192Comb.signComb

end VG.Impl.Ecdsa.X86
