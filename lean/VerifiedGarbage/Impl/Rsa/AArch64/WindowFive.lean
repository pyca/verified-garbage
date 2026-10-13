module

public import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-! Five-bit CRT exponentiation with a full-scan power table. -/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- Extract a five-bit digit from the packed exponent group. The shift is
fixed by the unrolled group, not by the secret exponent. -/
def groupDigit (shift : Nat) : List Instr :=
  [ldh .x3 Crt.sV, .lsr .x .x3 .x3 shift, movi .x4 31,
    .logic .and .x .x3 .x3 .x4, sth .x3 Crt.sNib]

/-- Append one byte to the 40-bit exponent group. -/
def groupByte (i : Nat) : List Instr :=
  [.ldrb .x5 .x3 i, .lsl .x .x4 .x4 8, .logic .orr .x .x4 .x4 .x5]

def groupBytes (n : Nat) : List Instr := (List.range n).flatMap groupByte

/-- Read the next five exponent bytes as one packed 40-bit group. -/
def loadGroup : List Instr :=
  ([ldh .x3 Crt.sExp, ldh .x4 Crt.sI, .add .x .x3 .x3 .x4, movi .x4 0] : List Instr) ++
    groupBytes 5 ++ [sth .x4 Crt.sV]

def wsEndT32 : List Instr :=
  VG.Impl.Rsa.AArch64.Crt.wsEnd ++ ([.lsl .x .x6 .x6 5, .add .x .x4 .x4 .x6] : List Instr)

open VG.Impl.Rsa.AArch64.Crt VG.Impl.Bignum.Public VG.Impl.Bignum.Crt in
/-- Reserve all 32 entries before placing the second prime workspace. -/
def primesSetup : List (Prog isa) :=
  [.block ([mov .x5 .x0] ++ wsEnd), .block (wsNew sWsP sPlen), .block ([ldh .x5 sWsP] ++ wsEndT32),
    .block (wsNew sWsQ sQlen), .block [enterP]] ++
  loadArr aN sP sPlen ++ loadArr aChunk sQinv sPlen ++ [.block [leave, enterQ]] ++
  loadArr aN sQ sQlen ++ [.block [leave]]

/-- Scalar fallback: scan all 32 entries regardless of the selected digit. -/
def tabSelect32 : List (Prog isa) :=
  [.block [ldh .x3 Crt.sTab, sth .x3 Crt.sEnt, movi .x3 0, sth .x3 Crt.sJ],
    .loop (seqs [
      .block ([ldh .x3 Crt.sJ, ldh .x4 Crt.sNib, .logic .eor .x .x3 .x3 .x4,
        movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0] ++
        VG.Impl.Rsa.AArch64.Crt.borrowMask ++ [ldh .x12 sW, ldh .x16 Crt.sEnt,
          ldh .x17 (sArr Crt.aT), mov .x14 .x12]),
      VG.Impl.Rsa.AArch64.Crt.selLoop,
      VG.Impl.Rsa.AArch64.Crt.nextEnt,
      .block [ldh .x3 Crt.sJ, .addImm .x .x3 .x3 1, sth .x3 Crt.sJ,
        .subImm .x .x4 .x3 32]]) (.nonzero .x .x4)]

open VG.Impl.Bignum.Public VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt in
def tabBuild32 (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [.block [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
    sth .x3 sTab, sth .x3 sEnt]] ++
  toEnt aY ++ [nextEnt] ++ toEnt aXc ++ copyArr aT aXc ++
  [.block [movi .x3 30, sth .x3 Crt.sBit],
    .loop (seqs ([mul aT aT aXc, nextEnt] ++ toEnt aT ++
      [.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]])) (.nonzero .x .x3)]

def windowCore (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa) : Prog isa :=
  seqs (List.replicate 5 (mul Public.aY Public.aY Public.aY) ++
    [select, mul Public.aY Public.aY Crt.aT])

/-- Finish a window by clearing the pending digit and bit counter. -/
def resetWindow : List Instr :=
  [movi .x3 0, sth .x3 Crt.sNib, sth .x3 Crt.sBit]

def windowBody (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa) : Prog isa :=
  .seq (windowCore mul select) (.block resetWindow)

/-- Consume fixed-position five-bit digits from most to least significant. -/
def groupWindows (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.seq (.block (groupDigit (5 * n))) (windowCore mul select))
      (groupWindows mul select n)

/-- Eight windows consume exactly the next five exponent bytes. -/
def batch (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa) : Prog isa :=
  .seq (.block loadGroup) (groupWindows mul select 8)

end VG.Impl.Rsa.AArch64.WindowFive
