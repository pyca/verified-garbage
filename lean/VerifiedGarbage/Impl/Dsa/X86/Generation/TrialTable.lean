module

public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Impl.RsaKeyGen.Primes32

/-! Initialize the shared packed trial-prime table in the parent workspace. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def trialTableStore (offset i : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 (RsaKeyGen.tabWord32 i))),
   .store (sc (offset + 4 * i)) .eax]

def trialTable (offset count : Nat) : List Instr :=
  (List.range count).flatMap (trialTableStore offset)

end VG.Impl.Dsa.X86.Generation
