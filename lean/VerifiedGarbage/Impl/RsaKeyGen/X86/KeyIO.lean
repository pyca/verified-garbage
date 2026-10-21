module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyCrt
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Impl.Bignum.X86.StoreBE

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

def writeArray (n j pointer length : Nat) : Prog isa := seqs [
  sel n j aZero j kOk,
  .block [.mov .ebx (.mem (sc pointer)), .mov .ecx (.mem (sc length))],
  VG.Impl.Bignum.X86.storeBE (slot n j)]

def outputIndex : Nat → Nat
  | 0 => aN
  | 1 => aD
  | 2 => aPa
  | 3 => aQa
  | 4 => aDp
  | 5 => aDq
  | _ => aQi

def writePort (n i : Nat) : Prog isa := writeArray n (outputIndex i) (8 * i) (8 * i + 4)

def writePorts (n : Nat) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, count + 1 => .seq (writePort n i) (writePorts n (i + 1) count)

/-- Rebuild the zero array after all inverse operations. The status is
separate from the masking bit, so retry writes zeros and returns two. -/
def writeOutputs (n : Nat) : Prog isa := seqs [
  zerosW (slot n aZero) (n + 2), writePorts n 0 7,
  .block [.mov .eax (.mem (sc kStatus))]]

def retry : Prog isa := .block [
  .mov .eax (.imm 0), .store (sc kOk) .eax,
  .mov .eax (.imm 2), .store (sc kStatus) .eax]

def keyPart (n : Nat) : Prog isa := seqs [
  qinvPart n, crtPart n, nPart n, finalMask n,
  .block [.mov .eax (.mem (sc kOk)), .store (sc kStatus) .eax]]

end VG.Impl.RsaKeyGen.X86.Key
