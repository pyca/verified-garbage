module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks

/-! Exact selected vector lookup, after digit recoding and before conditional negation. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

def lookupCode : List Instr := (outerBlock142.drop 76).take 564
def lookupProgram : Prog isa := .block lookupCode

end VG.Proof.Weierstrass.AArch64.P521Native
