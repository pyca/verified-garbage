module

public import VerifiedGarbage.Impl.Aes.InvCircuit
public import VerifiedGarbage.Impl.Aes.RISCV64.Linear
import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
meta import VerifiedGarbage.Impl.Aes.InvCircuit
meta import VerifiedGarbage.Impl.Aes.RISCV64.Alloc
meta import VerifiedGarbage.Impl.Aes.RISCV64.Linear

/-!
# The inverse round transformations of bitsliced AES on RISC-V

On the state of `Linear.lean` (four blocks in `q 0 … q 7`), as on x86-64
(`Impl/Aes/X86_64/Inv.lean`), and as BearSSL's `aes_ct64` (Thomas Pornin,
MIT licence) computes them for decryption:

* InvSubBytes: the circuit `Circuit.invSbox` (`Impl/Aes/InvCircuit.lean`),
  allocated as the S-box is (`Sbox.lean`), in the same registers and
  slots.
* InvShiftRows: rows 1 and 3 rotate the other way within their 16 bits,
  then rows 2 and 3 by 8 (which is its own inverse).
* InvMixColumns: MixColumns after multiplying each column by
  `{04}x² + {05}` (`invMcPre`): `a'ᵣ = aᵣ ⊕ {04} • (aᵣ ⊕ aᵣ₊₂)`, since
  `{0b}x³ + {0d}x² + {09}x + {0e} = ({03}x³ + {01}x² + {01}x + {02}) ({04}x² + {05})`
  modulo `x⁴ + 1`.

Each writes only the state registers and the S-box's temporaries.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64

/-- The register holding input word `k` during `invMcPre`. -/
def iv : Nat → Reg
  | 0 => .t0 | 1 => .t1 | 2 => .t2 | 3 => .t3
  | 4 => .t4 | 5 => .t5 | 6 => .t6 | _ => .a6

/-- The temporary of `invMcPre`'s rotations. -/
def ivt : Reg := .a7

/-- The inverse S-box on the state in `q 0 … q 7`, in place: the code
that `compile` allocates for `Circuit.invSbox`, written out as `sboxCode`
is. -/
def invSboxCode : List Instr := [
  xorR .t0 .s7 .s4, xorR .s6 .s6 .t0, notR .s6, xorR .t1 .s4 .s3, xorR .s5 .s5 .t1, notR .s5,
  xorR .t2 .s4 .s6, xorR .t3 .s3 .s6, xorR .t4 .t0 .t2, xorR .s3 .s3 .s0, notR .s3,
  xorR .s0 .t2 .s3, xorR .s4 .s4 .s3, xorR .s1 .s1 .s4, notR .s1, xorR .t5 .t3 .s1,
  xorR .t6 .t0 .t5, xorR .a6 .t4 .s1, xorR .a7 .s5 .a6, xorR .s8 .s4 .a7, xorR .s9 .s1 .s8,
  xorR .s7 .s7 .s2, xorR .s7 .t6 .s7, xorR .s2 .t1 .s7, xorR .s10 .a7 .s7, xorR .s11 .s0 .s7,
  stS 0 .s5, xorR .s5 .s8 .s11, stS 1 .s9, andR .s9 .t5 .s5, stS 2 .t5, andR .t5 .t0 .s6,
  xorR .t5 .t5 .s9, stS 3 .t0, andR .t0 .t6 .s10, xorR .t0 .t0 .s9, andR .s9 .s1 .s8, stS 4 .s1,
  andR .s1 .t4 .s4, xorR .s1 .s1 .s9, stS 5 .t4, andR .t4 .a6 .a7, xorR .t4 .t4 .s9,
  andR .s9 .t1 .s7, stS 6 .t1, andR .t1 .t3 .s11, xorR .t1 .t1 .s9, stS 7 .t3, andR .t3 .t2 .s0,
  xorR .t3 .t3 .s9, xorR .t5 .t5 .t1, xorR .t0 .t0 .t3, xorR .s1 .s1 .t1, xorR .t4 .t4 .t3,
  xorR .t5 .t5 .s2, xorR .t0 .t0 .s3, ldS .s3 1, xorR .s1 .s1 .s3, ldS .s3 0, xorR .t4 .t4 .s3,
  xorR .s3 .t5 .t0, andR .t5 .t5 .s1, xorR .s2 .t4 .t5, andR .t3 .s3 .s2, xorR .t3 .t3 .t0,
  xorR .t1 .s1 .t4, xorR .t0 .t0 .t5, andR .t0 .t0 .t1, xorR .t0 .t0 .t4, xorR .s1 .s1 .t0,
  xorR .t1 .s2 .t0, andR .t4 .t4 .t1, xorR .s1 .t4 .s1, xorR .s2 .s2 .t4, andR .s2 .t3 .s2,
  xorR .s3 .s3 .s2, xorR .s2 .s3 .s1, xorR .t4 .t3 .t0, xorR .t1 .t3 .s3, xorR .t5 .t0 .s1,
  xorR .s9 .t4 .s2, andR .s5 .t5 .s5, andR .s6 .s1 .s6, andR .s10 .t0 .s10, andR .s8 .t1 .s8,
  andR .s4 .s3 .s4, andR .a7 .t3 .a7, andR .s7 .t4 .s7, andR .s11 .s9 .s11, andR .s0 .s2 .s0,
  stS 0 .s11, ldS .s11 2, andR .t5 .t5 .s11, ldS .s11 3, andR .s1 .s1 .s11, andR .t0 .t0 .t6,
  ldS .t6 4, andR .t1 .t1 .t6, ldS .t6 5, andR .s3 .s3 .t6, andR .t3 .t3 .a6, ldS .a6 6,
  andR .t4 .t4 .a6, ldS .a6 7, andR .s9 .s9 .a6, andR .s2 .s2 .t2, xorR .s7 .s7 .t4,
  xorR .s7 .t1 .s7, xorR .s7 .s3 .s7, xorR .s7 .s9 .s7, xorR .s7 .s0 .s7, xorR .s8 .s8 .s7,
  xorR .a7 .a7 .s8, xorR .s4 .s4 .s8, xorR .s6 .s6 .s4, xorR .s1 .s10 .s1, xorR .s5 .s5 .s7,
  xorR .s10 .s10 .s5, xorR .s2 .t5 .s2, xorR .s7 .s6 .s1, xorR .t3 .t3 .s7, ldS .s7 0,
  xorR .s7 .s7 .s4, xorR .s0 .s0 .s7, xorR .s5 .a7 .s5, xorR .s6 .s6 .s5, xorR .s2 .t0 .s2,
  xorR .t4 .t4 .s2, xorR .t0 .t0 .t3, xorR .s3 .s3 .t0, xorR .s9 .s9 .s2, xorR .t1 .t1 .t0,
  xorR .t1 .s9 .t1, xorR .t5 .t5 .s1, xorR .s9 .s0 .s9, xorR .s5 .s5 .s9, xorR .t5 .t5 .s5,
  movR .s7 .a7, stS 0 .s6, movR .s6 .t1, movR .s5 .s3, movR .s4 .s10, movR .s3 .t5, ldS .s2 0,
  movR .s1 .s0, movR .s0 .t4]

#guard invSboxCode == compile sb Circuit.invSbox sboxIns sboxOuts sboxFree spillSlots

/-- The masks of InvShiftRows, and their first slot. -/
def invSrMasks : List (Nat × BitVec 64) :=
  [(1, 0x0000FFFF0000FFFF), (2, 0xFFF00000FFF00000), (3, 0x000F0000000F0000),
   (4, 0x00000000FFFFFFFF), (5, 0x00FF00FF00000000), (6, 0xFF00FF0000000000)]
def invSrSlot : Nat := 70

/-- InvShiftRows of one word: rows 1 and 3 rotate by 4 bits the other way
within their 16 bits, then rows 2 and 3 by 8. -/
def invSrWord (x : Reg) : List Instr :=
  [shlI t0 x 4, andR t0 t0 (m 2), shrI t1 x 12, andR t1 t1 (m 3),
   andR x x (m 1), xorR x x t0, xorR x x t1,
   shrI t0 x 8, andR t0 t0 (m 5), shlI t1 x 8, andR t1 t1 (m 6),
   andR x x (m 4), xorR x x t0, xorR x x t1]

def invShiftRows : List Instr :=
  loadMasks invSrSlot invSrMasks ++ (List.range 8).flatMap fun j => invSrWord (q j)

/-- The words of `{04} • u` (bit `j` of each byte), from those of `u`:
the multiplication by `x²`, reduced by `{1b}`. -/
def times4 (j : Nat) : List Nat :=
  match j with
  | 0 => [6] | 1 => [6, 7] | 2 => [0, 7] | 3 => [1, 6]
  | 4 => [2, 6, 7] | 5 => [3, 7] | 6 => [4] | _ => [5]

/-- Each column times `{04}x² + {05}`: with `uⱼ = qⱼ ⊕ (qⱼ ⋙ 32)` (the
byte and the one two rows down) in `iv j`, `qⱼ ⊕= ({04} • u)ⱼ`. -/
def invMcPre : List Instr :=
  ((List.range 8).flatMap fun j =>
    [shrI ivt (q j) 32, shlI (iv j) (q j) 32, xorR (iv j) (iv j) ivt, xorR (iv j) (iv j) (q j)]) ++
  ((List.range 8).flatMap fun j => (times4 j).map fun k => xorR (q j) (q j) (iv k))

def invMixColumns : List Instr := invMcPre ++ mixColumns

end VG.Impl.Aes.RISCV64
