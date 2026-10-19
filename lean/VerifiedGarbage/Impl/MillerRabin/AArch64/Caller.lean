module
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Layout
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
import VerifiedGarbage.Impl.Rsa.AArch64.CarrySelect
import VerifiedGarbage.Impl.Rsa.AArch64.Keys
import VerifiedGarbage.Impl.MillerRabin.AArch64.Round


/-! # Call a prepared round while retaining the caller's workspace base

The two padding words of Montgomery one hold the old x19 and return address.
The shared contract preserves that entire array. Its numeric value, read from
the first w words, stays one. No additional stack or public inputs are needed.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate

def saveLoad : List Instr := [ldh .x2 (sArr aOne), ldh .x3 sW]

def saveTail : List Instr :=
  [.lsl .x .x3 .x3 3, .add .x .x2 .x2 .x3,
    st .x19 .x2, st .x30 .x2 8, mov .x19 .x0,
    ldh .x1 sW, .addImm .x .x1 .x1 2, movi .x4 28, .mul .x .x1 .x1 .x4,
    .addImm .x .x1 .x1 32]

def save : List Instr := saveLoad ++ saveTail

def restoreHead : List Instr :=
  [.addImm .w .x3 .x0 0, mov .x0 .x19, movi .x4 0, .sub .x .x3 .x4 .x3, sth .x3 kFlag,
    ldh .x2 (sArr aOne), ldh .x3 sW]

def restoreTail : List Instr :=
  [.lsl .x .x3 .x3 3, .add .x .x2 .x2 .x3,
    ld .x30 .x2 8, ld .x19 .x2]

def restore : List Instr := restoreHead ++ restoreTail

def call (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block save) (.seq (.call name code) (.block restore))

end VG.Impl.MillerRabin.AArch64.Caller
