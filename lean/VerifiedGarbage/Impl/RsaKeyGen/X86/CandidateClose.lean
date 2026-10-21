module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Close
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Compare a candidate with the optional other RSA prime -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateClose
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def other (w : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (sc 20))])
    (.seq (Import.load (2 * w) (slot w 4))
      (Close.code (2 * w) (slot w 2) (slot w 3) (slot w 0) (slot w 4)))

def code (w : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc 24)), .alu .cmp .eax (.imm 0)])
    (.ite .e (.block [.mov .eax (.imm 0)]) (other w))

end VG.Impl.RsaKeyGen.X86.CandidateClose
