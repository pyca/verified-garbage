module

public import VerifiedGarbage.Impl.Camellia.Circuit
meta import VerifiedGarbage.Impl.Camellia.Circuit
public import VerifiedGarbage.Impl.Aes.AArch64.Sbox
meta import VerifiedGarbage.Impl.Aes.AArch64.Sbox

/-!
# The bitsliced Camellia S-box on AArch64

The circuit `Circuit.sbox` (`SBOX1`) on the eight words of the bitsliced
state (`q j` holds bit `j` of 64 bytes), in place: the code that the AES
allocator `compile` produces for it, with its temporaries (`x14`–`x17`,
`x19`–`x27`), all ones in `x28`, and spilling to the first slots of the
scratch buffer at `x5`. It is written out (and `#guard` checks that it is
what `compile` produces) so that the kernel, which evaluates the code in the
proofs, does not have to run the allocator.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in `q (7 - i)`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Camellia.Circuit.s i, q (7 - i))

/-- `SBOX1` on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .movz .x .x28 0 0, .subImm .x .x28 .x28 1, eorR .x14 .x13 .x7, eorR .x15 .x11 .x9,
  eorR .x16 .x8 .x14, eorR .x17 .x12 .x6, eorR .x19 .x6 .x15, eorR .x20 .x10 .x7,
  eorR .x21 .x10 .x16, eorR .x22 .x12 .x15, eorR .x23 .x8 .x17, eorR .x24 .x16 .x17,
  eorR .x25 .x13 .x12, eorR .x26 .x13 .x17, eorR .x26 .x26 .x28, eorR .x27 .x12 .x9, stS 0 .x26,
  eorR .x26 .x11 .x7, stS 1 .x13, eorR .x13 .x11 .x6, eorR .x11 .x11 .x16, eorR .x17 .x10 .x17,
  eorR .x10 .x10 .x25, eorR .x9 .x9 .x6, eorR .x9 .x9 .x28, eorR .x6 .x8 .x19, eorR .x8 .x8 .x20,
  eorR .x8 .x8 .x28, eorR .x25 .x7 .x22, eorR .x25 .x25 .x28, stS 2 .x25, eorR .x25 .x14 .x19,
  eorR .x14 .x14 .x22, eorR .x22 .x15 .x20, stS 3 .x25, eorR .x25 .x15 .x21, eorR .x15 .x15 .x24,
  stS 4 .x15, eorR .x15 .x16 .x19, eorR .x15 .x15 .x28, eorR .x16 .x16 .x27, eorR .x16 .x16 .x28,
  eorR .x19 .x19 .x20, eorR .x19 .x19 .x28, eorR .x13 .x21 .x13, eorR .x13 .x13 .x28,
  eorR .x26 .x23 .x26, eorR .x26 .x26 .x28, eorR .x23 .x23 .x22, eorR .x23 .x23 .x28, ldS .x22 1,
  eorR .x20 .x22 .x12, eorR .x20 .x20 .x28, eorR .x20 .x20 .x12, eorR .x22 .x22 .x7,
  eorR .x22 .x22 .x28, andR .x7 .x8 .x10, andR .x12 .x20 .x26, eorR .x12 .x12 .x7,
  andR .x27 .x21 .x13, eorR .x27 .x27 .x7, andR .x7 .x6 .x15, stS 1 .x6, andR .x6 .x14 .x11,
  eorR .x6 .x6 .x7, stS 5 .x14, andR .x14 .x24 .x9, eorR .x14 .x14 .x7, andR .x7 .x17 .x25,
  stS 6 .x17, andR .x17 .x19 .x23, eorR .x17 .x17 .x7, stS 7 .x19, ldS .x19 2, stS 8 .x24,
  ldS .x24 0, stS 9 .x21, andR .x21 .x19 .x24, eorR .x21 .x21 .x7, eorR .x12 .x12 .x17,
  eorR .x27 .x27 .x21, eorR .x6 .x6 .x17, eorR .x14 .x14 .x21, ldS .x21 4, eorR .x12 .x12 .x21,
  ldS .x21 3, eorR .x27 .x27 .x21, eorR .x6 .x6 .x22, eorR .x14 .x14 .x16, eorR .x16 .x12 .x27,
  andR .x12 .x12 .x6, eorR .x22 .x14 .x12, andR .x21 .x16 .x22, eorR .x21 .x21 .x27,
  eorR .x17 .x6 .x14, eorR .x27 .x27 .x12, andR .x27 .x27 .x17, eorR .x27 .x27 .x14,
  eorR .x6 .x6 .x27, eorR .x17 .x22 .x27, andR .x14 .x14 .x17, eorR .x6 .x14 .x6,
  eorR .x22 .x22 .x14, andR .x22 .x21 .x22, eorR .x16 .x16 .x22, eorR .x22 .x16 .x6,
  eorR .x14 .x21 .x27, eorR .x17 .x21 .x16, eorR .x12 .x27 .x6, eorR .x7 .x14 .x22,
  andR .x10 .x12 .x10, andR .x26 .x6 .x26, andR .x13 .x27 .x13, andR .x15 .x17 .x15,
  andR .x11 .x16 .x11, andR .x9 .x21 .x9, andR .x25 .x14 .x25, andR .x23 .x7 .x23,
  andR .x24 .x22 .x24, andR .x12 .x12 .x8, andR .x6 .x6 .x20, ldS .x20 9, andR .x27 .x27 .x20,
  ldS .x20 1, andR .x17 .x17 .x20, ldS .x20 5, andR .x16 .x16 .x20, ldS .x20 8,
  andR .x21 .x21 .x20, ldS .x20 6, andR .x14 .x14 .x20, ldS .x20 7, andR .x7 .x7 .x20,
  andR .x22 .x22 .x19, eorR .x23 .x26 .x23, eorR .x15 .x15 .x9, eorR .x19 .x25 .x24,
  eorR .x20 .x10 .x7, eorR .x27 .x27 .x23, eorR .x8 .x17 .x15, stS 2 .x15, eorR .x15 .x14 .x19,
  eorR .x21 .x13 .x21, eorR .x25 .x25 .x22, eorR .x24 .x24 .x12, eorR .x12 .x12 .x6,
  eorR .x16 .x16 .x8, eorR .x7 .x7 .x15, stS 7 .x7, eorR .x7 .x20 .x27, eorR .x10 .x10 .x13,
  eorR .x26 .x26 .x11, eorR .x9 .x9 .x20, eorR .x6 .x6 .x25, eorR .x17 .x17 .x27,
  eorR .x14 .x14 .x23, eorR .x22 .x22 .x24, ldS .x23 2, eorR .x23 .x23 .x12, eorR .x10 .x19 .x10,
  eorR .x8 .x8 .x21, eorR .x15 .x15 .x12, eorR .x21 .x21 .x24, eorR .x25 .x25 .x14, ldS .x14 7,
  eorR .x24 .x16 .x14, eorR .x16 .x16 .x7, eorR .x11 .x14 .x23, eorR .x11 .x11 .x28,
  eorR .x7 .x7 .x6, eorR .x7 .x7 .x28, eorR .x26 .x26 .x9, eorR .x9 .x17 .x21, eorR .x9 .x9 .x28,
  eorR .x22 .x22 .x16, eorR .x22 .x22 .x28, eorR .x13 .x8 .x25, eorR .x12 .x15 .x26,
  eorR .x12 .x12 .x28, movR .x8 .x7, movR .x7 .x22, movR .x6 .x24]

#guard sboxCode == compile sb VG.Impl.Camellia.Circuit.sbox sboxIns sboxOuts sboxFree ones spillSlots

end VG.Impl.Camellia.AArch64
