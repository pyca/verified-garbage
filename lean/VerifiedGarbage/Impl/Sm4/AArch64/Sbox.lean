module

public import VerifiedGarbage.Impl.Sm4.Circuit
meta import VerifiedGarbage.Impl.Sm4.Circuit
public import VerifiedGarbage.Impl.Aes.AArch64.Sbox
meta import VerifiedGarbage.Impl.Aes.AArch64.Sbox

/-!
# The bitsliced SM4 S-box on AArch64

The circuit `Circuit.sbox` on the eight planes of the state (`q j` holds bit
`j` of 64 bytes), in place: the code that the AES allocator `compile`
produces for it, with its temporaries (`x14`–`x17`, `x19`–`x27`), all ones
in `x28`, and spilling to the first slots of the scratch buffer at `x5`. It
is written out (and `#guard` checks that it is what `compile` produces) so
that the kernel, which evaluates the code in the proofs, does not have to
run the allocator.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

/-- The circuit's input `xᵢ` and output `sᵢ` are bit `7 - i`, in `q (7 - i)`. -/
def sboxIns : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.x i, q (7 - i))
def sboxOuts : List (Nat × Reg) := (List.range 8).map fun i => (VG.Impl.Sm4.Circuit.s i, q (7 - i))

/-- The S-box on the state in `q 0 … q 7`, in place. -/
def sboxCode : List Instr := [
  .movz .x .x28 0 0, .subImm .x .x28 .x28 1, eorR .x14 .x10 .x8, eorR .x15 .x9 .x6,
  eorR .x16 .x7 .x15, eorR .x17 .x13 .x14, eorR .x19 .x11 .x16, eorR .x20 .x12 .x8,
  eorR .x10 .x13 .x10, eorR .x21 .x11 .x17, eorR .x22 .x12 .x21, eorR .x23 .x13 .x9,
  eorR .x24 .x12 .x10, eorR .x25 .x11 .x14, eorR .x21 .x7 .x21, eorR .x21 .x21 .x28,
  eorR .x26 .x15 .x17, eorR .x27 .x6 .x24, eorR .x24 .x19 .x24, stS 0 .x24, eorR .x24 .x7 .x20,
  eorR .x12 .x12 .x26, eorR .x6 .x6 .x17, eorR .x6 .x6 .x28, eorR .x26 .x7 .x23, eorR .x9 .x9 .x25,
  eorR .x9 .x9 .x28, eorR .x10 .x16 .x10, stS 1 .x17, eorR .x17 .x14 .x19, stS 2 .x17,
  eorR .x17 .x19 .x20, eorR .x8 .x13 .x8, eorR .x8 .x8 .x28, eorR .x27 .x7 .x27,
  eorR .x27 .x27 .x28, eorR .x15 .x15 .x25, eorR .x11 .x11 .x23, eorR .x11 .x11 .x28,
  eorR .x23 .x7 .x22, eorR .x14 .x14 .x16, eorR .x14 .x14 .x28, eorR .x13 .x13 .x16,
  eorR .x13 .x13 .x28, andR .x16 .x23 .x21, andR .x25 .x19 .x9, eorR .x25 .x25 .x16, stS 3 .x19,
  andR .x19 .x12 .x26, eorR .x19 .x19 .x16, andR .x16 .x7 .x15, stS 4 .x7, andR .x7 .x20 .x11,
  eorR .x7 .x7 .x16, stS 5 .x20, andR .x20 .x24 .x6, eorR .x20 .x20 .x16, andR .x16 .x10 .x14,
  stS 6 .x10, andR .x10 .x22 .x13, eorR .x10 .x10 .x16, stS 7 .x22, ldS .x22 1, stS 8 .x24,
  andR .x24 .x17 .x22, eorR .x24 .x24 .x16, eorR .x25 .x25 .x10, eorR .x19 .x19 .x24,
  eorR .x7 .x7 .x10, eorR .x20 .x20 .x24, eorR .x25 .x25 .x8, ldS .x8 0, eorR .x19 .x19 .x8,
  ldS .x8 2, eorR .x7 .x7 .x8, eorR .x20 .x20 .x27, eorR .x27 .x25 .x19, andR .x25 .x25 .x7,
  eorR .x8 .x20 .x25, andR .x24 .x27 .x8, eorR .x24 .x24 .x19, eorR .x10 .x7 .x20,
  eorR .x19 .x19 .x25, andR .x19 .x19 .x10, eorR .x19 .x19 .x20, eorR .x7 .x7 .x19,
  eorR .x10 .x8 .x19, andR .x20 .x20 .x10, eorR .x7 .x20 .x7, eorR .x8 .x8 .x20, andR .x8 .x24 .x8,
  eorR .x27 .x27 .x8, eorR .x8 .x27 .x7, eorR .x20 .x24 .x19, eorR .x10 .x24 .x27,
  eorR .x25 .x19 .x7, eorR .x16 .x20 .x8, andR .x21 .x25 .x21, andR .x9 .x7 .x9,
  andR .x26 .x19 .x26, andR .x15 .x10 .x15, andR .x11 .x27 .x11, andR .x6 .x24 .x6,
  andR .x14 .x20 .x14, andR .x13 .x16 .x13, andR .x22 .x8 .x22, andR .x25 .x25 .x23, ldS .x23 3,
  andR .x7 .x7 .x23, andR .x19 .x19 .x12, ldS .x12 4, andR .x10 .x10 .x12, ldS .x12 5,
  andR .x27 .x27 .x12, ldS .x12 8, andR .x24 .x24 .x12, ldS .x12 6, andR .x20 .x20 .x12, ldS .x12 7,
  andR .x16 .x16 .x12, andR .x8 .x8 .x17, eorR .x25 .x25 .x20, eorR .x14 .x14 .x7,
  eorR .x6 .x21 .x6, eorR .x17 .x27 .x14, eorR .x24 .x24 .x17, eorR .x22 .x9 .x22,
  eorR .x17 .x13 .x24, eorR .x8 .x8 .x25, eorR .x12 .x11 .x6, eorR .x23 .x17 .x8, stS 7 .x11,
  eorR .x11 .x19 .x12, stS 6 .x23, eorR .x23 .x16 .x22, eorR .x25 .x25 .x23, eorR .x6 .x15 .x6,
  eorR .x6 .x25 .x6, eorR .x19 .x19 .x8, eorR .x27 .x27 .x16, eorR .x10 .x10 .x20,
  eorR .x14 .x14 .x12, eorR .x22 .x22 .x11, eorR .x24 .x24 .x22, eorR .x24 .x24 .x28,
  eorR .x7 .x7 .x6, eorR .x26 .x26 .x17, eorR .x6 .x13 .x7, eorR .x6 .x6 .x28, eorR .x13 .x27 .x10,
  eorR .x13 .x13 .x28, eorR .x21 .x21 .x9, ldS .x9 6, eorR .x15 .x15 .x9, eorR .x9 .x9 .x21,
  eorR .x12 .x11 .x26, eorR .x12 .x12 .x28, ldS .x26 7, eorR .x8 .x26 .x15, eorR .x10 .x25 .x14,
  eorR .x10 .x10 .x28, movR .x11 .x9, movR .x9 .x19, movR .x7 .x24]

#guard sboxCode == compile sb VG.Impl.Sm4.Circuit.sbox sboxIns sboxOuts sboxFree ones spillSlots

end VG.Impl.Sm4.AArch64
