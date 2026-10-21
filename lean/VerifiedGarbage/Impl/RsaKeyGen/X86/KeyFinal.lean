module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

/-! # Native final validity masks for RSA key assembly -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys

def andFlag : Prog isa := .block (andS kOk kOk kFlag)

def withFlag (c : Prog isa) : Prog isa := .seq c andFlag

def topBit (n : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot n aN + 4 * (n - 1)))), .shift .shr .eax 31,
    .store (sc kFlag) .eax]

/-- `e < 2^33` iff the high native word is below two. -/
def exponentUpper : List Instr :=
  [.mov .eax (.mem (sc kEvHi)), .alu .cmp .eax (.imm 2),
    .alu .sbb .eax (.reg .eax), .alu .and .eax (.imm 1), .store (sc kFlag) .eax]

def exponentAtLeastThree (n : Nat) : Prog isa := seqs [
  constArray n aT1 3, sub3 n aT2 aE aT1,
  .block [.mov .eax (.mem (sc kOk)), .store (sc kFlag) .eax], .block borrowMask]

def finalMask (n : Nat) : Prog isa := seqs [
  withFlag (.block (topBit n)),
  withFlag (.block (bitOf n kFlag aPa)),
  withFlag (.block (bitOf n kFlag aQa)),
  withFlag (.block (bitOf n kFlag aE)),
  withFlag (.block exponentUpper),
  exponentAtLeastThree n]

end VG.Impl.RsaKeyGen.X86.Key
