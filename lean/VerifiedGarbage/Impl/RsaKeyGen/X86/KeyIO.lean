module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Impl.Bignum.X86.StoreBE
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent

/-! # Native prime import and masked big-endian key export -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Rsa.X86.Keys

def kStatus : Nat := 96

/-- Import at prime width, then widen into the persistent bank. -/
def loadPrime (n pointer out : Nat) : Prog isa := seqs [
  .block [.mov .esi (.mem (sc pointer))],
  VG.Impl.RsaKeyGen.X86.Import.load (n / 2) (slot n 0),
  widenCopy n (n / 2) out (slot n 0)]

def outputIndex : Nat → Nat
  | 0 => aN
  | 1 => aD
  | 2 => aPa
  | 3 => aQa
  | 4 => aDp
  | 5 => aDq
  | _ => aQi

def retry : Prog isa := .block [
  .mov .eax (.imm 0), .store (sc kOk) .eax,
  .mov .eax (.imm 2), .store (sc kStatus) .eax]

end VG.Impl.RsaKeyGen.X86.Key
