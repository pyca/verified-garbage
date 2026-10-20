module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! Reject undersized p candidates before consuming any witnesses. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- x3 is zero exactly when the saved candidate has fewer than L bits. -/
def candidateWidth : List Instr := [ldh .x1 20, .ldrb .x3 .x1 0, .lsr .x .x3 .x3 7]

end VG.Impl.Dsa.AArch64.Generation
