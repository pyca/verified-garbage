module

public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Public metadata shared by candidate preparation and all witnesses

The prepared Montgomery and Miller–Rabin kernels use 64-bit header fields
even on i686. Addresses and lengths fit in 32 bits, so every high half is
explicitly zeroed. The inverse is prepared separately and is never cleared
by this initialization. EDI remains the workspace base.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Header
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def literal (offset value : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 value)), .store (sc offset) .eax,
    .store (sc (offset + 4)) .edx]

def pointer (w i : Nat) : List Instr :=
  [.mov .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 (slot w i))),
    .store (sc (64 + 8 * i)) .eax, .store (sc (68 + 8 * i)) .edx]

def code (w : Nat) : List Instr :=
  [.mov .edx (.imm 0)] ++ literal 48 w ++ literal 224 (stride w) ++
    (List.range 8).flatMap (pointer w)

end VG.Impl.RsaKeyGen.X86.Header
