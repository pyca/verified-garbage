module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Witness
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes

/-! Copy the significant suffix and advance past the entire padded witness draw. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

/-- ESI points to the draw; the 160-bit case skips four of its 24 bytes. -/
def drawCopy (len drawBytes : Nat) : Prog isa :=
  .seq (.block [.alu .add .esi (.imm (BitVec.ofNat 32 (drawBytes - len))),
      .mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 Dsa.Generation.Layout.witness)),
      .mov .ecx (.imm (BitVec.ofNat 32 len))]) VG.Impl.Bignum.X86.copyBytes

end VG.Impl.Dsa.X86.Generation
