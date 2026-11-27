module

public import VerifiedGarbage.Impl.Ecdsa.P384.X86
public import VerifiedGarbage.Impl.P384.CombTable7

/-! # P-384's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

/-- The comb's tables, for the comb by complete additions. -/
def p384d : CombData := ⟨7, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start, "VG_P384_COMB", false⟩

def p384Comb : Cfg := { p384 with comb := some p384d }

/-- `vg_ecdsa_p384_sign_k`. -/
def signP384Comb : Prog isa := p384Comb.signComb

end VG.Impl.Ecdsa.X86
