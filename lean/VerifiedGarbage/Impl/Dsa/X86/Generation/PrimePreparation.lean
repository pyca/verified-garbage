module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MontgomeryConstants
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Transfer
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactHeader
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactInverse

/-! Prepare a candidate once, retaining its Montgomery context for all witnesses. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def enterArithmetic : List Instr :=
  [.alu .add .edi (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.arithmetic))]

def leaveArithmetic : List Instr :=
  [.alu .sub .edi (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.arithmetic))]

def factorCandidate (n : Nat) : Prog isa :=
  .seq (.block (enterArithmetic ++ [.mov .esi (.imm (BitVec.ofNat 32 (8 * n)))]))
    (.seq (withArithmetic (prepareCandidateExponent arithmeticLay)) (.block leaveArithmetic))

def primePrefix (n bits : Nat) : Prog isa :=
  .seq (montgomeryConstants n bits) (.seq (candidateTransfer n).code (factorCandidate n))

/-- The parent holds the candidate in dynamic slot zero. After preparation,
the compact workspace has its constants and exponent; each witness is encoded
separately before calling the shared Miller–Rabin round. -/
def primePreparation (n bits : Nat) : Prog isa :=
  [primePrefix n bits,
   transferWords (saveExponentTransfers n),
   .block (enterArithmetic ++ compactHeader n ++ leaveArithmetic),
   transferWords (compactTransfers n),
   .block ([.mov .ecx (.mem (sc 0))] ++ enterArithmetic ++ compactInverse ++ leaveArithmetic)
  ].foldr .seq (.block [])

end VG.Impl.Dsa.X86.Generation
