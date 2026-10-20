module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Layout
import VerifiedGarbage.Impl.Rsa.AArch64.Keys

/-! Copy the significant bytes and consume the complete witness draw. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def drawCopyArgs (len drawBytes : Nat) : List Instr :=
  [mov .x17 .x0, ldh .x12 kRand, ldh .x3 kUsed, .add .x .x12 .x12 .x3,
   .addImm .x .x12 .x12 (drawBytes - len), .addImm .x .x3 .x3 drawBytes, sth .x3 kUsed,
   ldh .x2 kOut, movi .x9 len]

/-- A q160 draw consumes 24 bytes, skipping its four high bytes. -/
def drawCopy (len drawBytes : Nat) : Prog isa :=
  .seq (.block (drawCopyArgs len drawBytes))
    (.seq Random.copyRest (.block [mov .x0 .x17]))

end VG.Impl.Dsa.AArch64.Generation
