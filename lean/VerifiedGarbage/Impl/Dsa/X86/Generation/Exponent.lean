module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Halving
public import VerifiedGarbage.Impl.Bignum.X86.TwoPower

/-! Prepare the shared Miller–Rabin round's four-bit-window exponent. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def exponentSigma : List Instr :=
  [.mov .eax (.mem (sc 20)), .alu .sub .eax (.imm 1), .alu .and .eax (.imm 3),
   .alu .add .eax (.imm 1), .store (sc 32) .eax]

def exponentMask (threshold : Nat) : List Instr :=
  [.mov .eax (.mem (sc 32)), .alu .sub .eax (.imm (BitVec.ofNat 32 (threshold + 1))),
   .shift .shr .eax 31, .alu .xor .eax (.imm 1), .store (sc 28) .eax]

def exponentHalf (L : Rsa.X86.KeyRt.Lay) (threshold : Nat) : Prog isa :=
  .seq (.block (exponentMask threshold))
    (.seq (halvingPrepare L) (Rsa.X86.KeyRt.sel L 0 0 1 28))

def exponentStart (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (.block exponentSigma)
    (.seq (Rsa.X86.KeyRt.copy L 0 2)
      (.seq (.block [.mov .ebx (.imm 0)]) (Rsa.X86.KeyRt.half L 0)))

/-- Array two retains the candidate; header20 is its factor-of-two count. -/
def exponentSetup (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (exponentStart L)
    (.seq (exponentHalf L 1) (.seq (exponentHalf L 2) (exponentHalf L 3)))

/-- Retain both halves of the round's one-hot metadata in the header. -/
def exponentOneHot : List Instr :=
  [.mov .ecx (.mem (sc 20))] ++ Bignum.X86.TwoPower.code ++
  [.store (sc 64) .eax, .store (sc 68) .edx]

def prepareExponent (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (exponentSetup L) (.block exponentOneHot)

def candidateExponentStart (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (Rsa.X86.KeyRt.copy L 2 0)
    (.block (Rsa.X86.KeyRt.clrLow L 0))

/-- Save the odd candidate, clear its low bit to obtain c-1, and reuse the
fixed-schedule factorization before preparing the shared round exponent. -/
def prepareCandidateExponent (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (candidateExponentStart L) (.seq (halving L) (prepareExponent L))

end VG.Impl.Dsa.X86.Generation
