module
public import VerifiedGarbage.Impl.MdStream.X86_64


/-! Word-sized operations on PSS's small buffers. -/

@[expose] public section

namespace VG.Impl.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.MdStream.X86_64

def copyWord64 (src dst : Reg) (so doff j : Nat) : List Instr :=
  [.mov .rax (.mem (at_ src (so + 8 * j))), .store (at_ dst (doff + 8 * j)) .rax]

def copyWords64 (src dst : Reg) (so doff n : Nat) : List Instr :=
  (List.range n).flatMap (copyWord64 src dst so doff)

end VG.Impl.RsaPss.X86_64
