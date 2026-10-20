module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Impl.Dsa.X86.Generate

/-! # Pack p, q, and g for the existing verified domain checker -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def packArgs (src dst len : Nat) : List Instr :=
  bufferPointer .esi src ++ bufferPointer .edx dst ++
    [.mov .ecx (.imm (BitVec.ofNat 32 len)), .mov .ebx (.imm (-1))]

def packPart (src dst len : Nat) : Prog isa := .seq (.block (packArgs src dst len)) Generate.copyMasked

def pack (plen qlen : Nat) : Prog isa :=
  .seq (packPart VG.Impl.Dsa.Generation.Layout.p VG.Impl.Dsa.Generation.Layout.packed plen)
    (.seq (packPart VG.Impl.Dsa.Generation.Layout.q (VG.Impl.Dsa.Generation.Layout.packed + plen) qlen)
      (packPart VG.Impl.Dsa.Generation.Layout.g (VG.Impl.Dsa.Generation.Layout.packed + plen + qlen) plen))
end VG.Impl.Dsa.X86.Generation
