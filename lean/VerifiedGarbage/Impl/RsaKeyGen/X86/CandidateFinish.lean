module

public import VerifiedGarbage.Impl.Bignum.X86.StoreBE
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Candidate status and used-byte output on the native cdecl ABI -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def writeUsed : List Instr :=
  [.store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax]

def none : Prog isa := .seq (.block [.mov .edx (.mem (sc 44)), .mov .eax (.imm 0)]) (.block writeUsed)

def used (status : Nat) : Prog isa :=
  .seq (.block [.mov .edx (.mem (sc 44)), .mov .eax (.mem (sc 152))])
    (.seq (.block writeUsed) (.block [.mov .eax (.imm (BitVec.ofNat 32 status))]))

def prime (w : Nat) : Prog isa :=
  .seq (.block [.mov .ebx (.mem (sc 0)), .mov .ecx (.mem (sc 4))])
    (.seq (VG.Impl.Bignum.X86.storeBE (slot w 0)) (used 1))

def mrResult (w : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc 168)), .alu .cmp .eax (.imm 1)])
    (.ite .e (prime w) (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e none (used 3))))

end VG.Impl.RsaKeyGen.X86.CandidateFinish
