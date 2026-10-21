module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateImport
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Import the first random block and initialize its consumed-byte count -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateLoad
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def count (w : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 (8 * w))), .store (sc 152) .eax,
    .mov .eax (.imm 0), .store (sc 156) .eax]

def code (w : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (sc 28))])
    (.seq (CandidateImport.code w (slot w 0)) (.block (count w)))

end VG.Impl.RsaKeyGen.X86.CandidateLoad
