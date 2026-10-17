module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # DSA's fixed-width big-endian components on 32-bit x86

Every supported component width is a multiple of four bytes, so a component
is a loop over its 32-bit words, read and written through `ebx`, from its
last word down, byte-reversed. `esi` points to the component.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- `[out]` (`2 n` words) = the big-endian `len` bytes at `esi`. -/
def loadComponent (len n out : Nat) : Prog isa :=
  .seq (.block [.mov .ebx (.reg .esi), .alu .add .ebx (.imm (BitVec.ofNat 32 (len - 4)))]) <|
  .seq (wordLoop (len / 4) [.mov .eax (.mem (at_ .ebx 0)), .bswap .eax,
    .store (at_ .ebp out) .eax, .alu .sub .ebx (.imm 4)])
    (.block ((List.range (2 * n - len / 4)).flatMap fun j =>
      [.mov .eax (.imm 0), .store (sc (out + 4 * (len / 4 + j))) .eax]))

/-- The big-endian `len` bytes at `esi` = `[input]` masked with `ecx`. -/
def storeComponent (len input : Nat) : Prog isa :=
  .seq (.block [.mov .ebx (.reg .esi), .alu .add .ebx (.imm (BitVec.ofNat 32 (len - 4)))])
    (wordLoop (len / 4) [.mov .eax (.mem (at_ .ebp input)), .alu .and .eax (.reg .ecx), .bswap .eax,
      .store (at_ .ebx 0) .eax, .alu .sub .ebx (.imm 4)])

end VG.Impl.Dsa.X86
