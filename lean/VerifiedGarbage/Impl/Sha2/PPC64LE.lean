module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # Paired SHA-2 message scheduling on PPC64LE -/

@[expose] public section
namespace VG.Impl.Sha2.PPC64LE
open VG.PPC64LE

/-- Each vector holds two consecutive schedule words. -/
def pairs : List VReg := [.v0, .v1, .v2, .v3, .v16, .v17, .v18, .v19]

def preg (n : Nat) : VReg := pairs.getD (n % 8) .v0

/-- Generate two schedule words at once, retaining all sixteen words in vectors. -/
def schedulePair (wide : Bool) (n : Nat) : List Instr :=
  let p := preg n
  let stride := if wide then 16 else 8
  let size := if wide then 8 else 4
  let width := if wide then Size.d else Size.w
  if n < 8 then [
    .li .r0 (stride*n), .loadRev width .r16 .r4 .r0,
    .li .r0 (stride*n+size), .loadRev width .r17 .r4 .r0,
    .mtvsrd p .r16, .mtvsrd .v12 .r17,
    .vop (.sldoi p p p 8), .vop (.sldoi p p .v12 8)]
  else [
    .vop (if wide then .sha512 .v12 (preg (n+7)) false 10 else .sha256 .v12 (preg (n+7)) false 5),
    .vop (.sldoi .v13 p (preg (n+1)) 8),
    .vop (if wide then .sha512 .v13 .v13 false 0 else .sha256 .v13 .v13 false 0),
    .vop (.sldoi .v14 (preg (n+4)) (preg (n+5)) 8),
    .vop (.add wide .v12 .v12 p), .vop (.add wide .v12 .v12 .v13),
    .vop (.add wide p .v12 .v14)]


end VG.Impl.Sha2.PPC64LE
