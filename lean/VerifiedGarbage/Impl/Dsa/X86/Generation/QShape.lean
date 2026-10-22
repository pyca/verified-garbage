module

public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Shape a copied digest into an odd, full-width subgroup candidate -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def forceByte (r : Reg) (mask : BitVec 8) : List Instr :=
  [.movzx8 .eax (at_ r 0), .alu .or .eax (.imm (mask.setWidth 32)), .store8 (at_ r 0) .al]

/-- `esi` is the digest, `ebx` its disjoint destination, and `ecx` its nonzero length. -/
def qShape : Prog isa :=
  .seq (.block [.mov .ebp (.reg .ebx)])
    (.seq VG.Impl.Bignum.X86.copyBytes
      (.seq (.block (forceByte .ebp 128))
        (.block ([.alu .sub .ebx (.imm 1)] ++ forceByte .ebx 1))))

end VG.Impl.Dsa.X86.Generation
