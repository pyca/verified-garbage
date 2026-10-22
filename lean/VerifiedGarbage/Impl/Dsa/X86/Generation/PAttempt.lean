module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PConstruct
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CheckCandidate

/-! Width rejection precedes primality testing and consumes no witness bytes. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

def candidateWidth : List Instr :=
  [.movzx8 .eax (sc Dsa.Generation.Layout.p), .alu .cmp .eax (.imm 128)]

def pTest (name : String) (code : Prog isa) (n : Nat) : Prog isa :=
  .seq (.block candidateWidth) (.ite .b (.block (setHeader primeStatus 3))
    (checkCandidate name code n (8 * n) Dsa.Generation.Layout.p))

def pAttempt (H : Hash) (name : String) (code : Prog isa) (seedLen n : Nat) : Prog isa :=
  .seq (pConstruct H seedLen n) (pTest name code n)

end VG.Impl.Dsa.X86.Generation
