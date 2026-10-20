module
public import VerifiedGarbage.Impl.Rsa.X86.Div

/-! # Fixed-width arithmetic for a DSA p candidate

The quotient/remainder step handles the even divisor 2q without Montgomery
arithmetic. Its quotient is reused to form the generator exponent.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def candidateQuotient : Nat := 0
def candidateRemainder : Nat := 512
def candidateDivisor : Nat := 1024
def candidateTemporary : Nat := 1536
def candidateOriginal : Nat := 2048
def candidateP : Nat := 2560

def doubleWords (n dst tmp : Nat) : Prog isa :=
  .seq (chainW .adc n tmp dst dst) (VG.Impl.Rsa.X86.Div.copyWords n tmp dst)

def incrementEven (dst : Nat) : List Instr :=
  [.mov .eax (.mem (sc dst)), .alu .add .eax (.imm 1), .store (sc dst) .eax]

/-- Input: X in quotient, 2q in divisor (n+1 words). Output: p and (p-1)/q. -/
def reduceCandidate (n : Nat) : Prog isa :=
  .seq (VG.Impl.Rsa.X86.Div.copyWords n candidateQuotient candidateOriginal)
    (.seq (VG.Impl.Rsa.X86.Div.code n candidateQuotient candidateRemainder candidateDivisor candidateTemporary)
      (.seq (.seq (chainW .sbb n candidateP candidateOriginal candidateRemainder)
        (.block (incrementEven candidateP))) (doubleWords n candidateQuotient candidateTemporary)))
end VG.Impl.Dsa.X86.Generation
