module
public import VerifiedGarbage.Impl.Dsa.X86.Bytes

/-! # Serialize a public parameter-generation intermediate -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86

def storePublic (len input : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm (BitVec.allOnes 32))]) (storeComponent len input)
end VG.Impl.Dsa.X86.Generation
