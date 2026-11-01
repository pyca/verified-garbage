module

public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-!
# GHASH: RISC-V implementation

`vg_ghash(h = a0, y = a1, data = a2, n = a3, scratch = a4)`.

For each of the `n` blocks `X` at `data`, `Y := (Y ⊕ X) • H`, where `•` is
SP 800-38D Algorithm 1 (`Spec.Gcm.mul`): with `Vᵢ` the values Algorithm 1
gives `V` (`V₀ = H`, `Vᵢ₊₁ = Vᵢ >> 1`, XORed with `R` if `LSB₁(Vᵢ) = 1`),
which depend only on `H`, the product is the XOR of the `Vᵢ` for which bit
`xᵢ` (from the left) of `Y ⊕ X` is set.

* A 128-bit value is two 64-bit words, the most significant first.
* The base ISA has no carry-less multiplication, and its multiplier is slow
  on some cores, so the code multiplies with loads, shifts and logic only:
  it writes the table of `V₀ … V₁₂₇` to a frame of 2048 bytes on the stack
  (`Vᵢ` at `sp + 16 i`, its words in `ld` order), and then each bit costs a
  mask (`slli` and `srai`), two loads and four logic instructions.
* `table`: `V` in `a6`/`a7`, stored and stepped 8 times per iteration, the
  reduction constant `R` (its top byte `0xE1`) in `t6`.
* `mul`: `Z` in `a4`/`a5`, `x = Y ⊕ X` in `a6`/`a7`; each iteration uses
  the top byte of `x` (bit `k` from the left in the sign of `x << k`,
  which `srai` turns into the mask), the 8 entries of the table at `t4`,
  and shifts `x` left by a byte. `Y` stays in `a4`/`a5` from block to
  block, and is written back to `y` at the end.
* Each table pointer reaches the end of the frame (`t5`) after 16
  iterations.
* The table is zeroed before the frame is popped.
* The pointers and the block count are public, and so is everything
  computed from them; no address and no branch depends on anything else.
  Unaligned buffers are read and written a byte at a time.
-/

@[expose] public section

namespace VG.Impl.Gcm.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadBE64 storeBE)

/-! ## Registers -/

def HP : Reg := .a0
def YP : Reg := .a1
def DP : Reg := .a2
def N : Reg := .a3
/-- `Z`, the high word and the low word. -/
def Z0 : Reg := .a4
def Z1 : Reg := .a5
/-- `V` while the table is written, then `x = Y ⊕ X`. -/
def X0 : Reg := .a6
def X1 : Reg := .a7
/-- The words of a table entry. -/
def U0 : Reg := .t0
def U1 : Reg := .t1
/-- The mask. -/
def M : Reg := .t2
/-- A temporary. -/
def T : Reg := .t3
/-- The table pointer, and the end of the table. -/
def P : Reg := .t4
def E : Reg := .t5
/-- `R`'s high word. -/
def RR : Reg := .t6

/-! ## The table -/

/-- Store `V` as entry `k` (of 8) at `P`, and step it: `V := V >> 1`, XORed
with `R` if its lowest bit was set. -/
def tabStep (k : Nat) : List Instr :=
  [.store .d X0 P (16 * k), .store .d X1 P (16 * k + 8),
   .shift .sll .d M X1 63, .shift .sra .d M M 63, .logic .and M M RR,
   .shift .sll .d T X0 63, .shift .srl .d X1 X1 1, .logic .or X1 X1 T,
   .shift .srl .d X0 X0 1, .logic .xor X0 X0 M]

/-- Eight entries, and the pointer advanced past them. -/
def tabBody : List Instr :=
  (List.range 8).flatMap tabStep ++ [.addi P P 128]

/-- `V := H`, `R`, and the pointers to the frame and its end. -/
def tabInit : List Instr :=
  loadBE64 X0 T HP 0 ++ loadBE64 X1 T HP 8 ++
    [.li RR (-31), .shift .sll .d RR RR 56, .addSp P 0, .addi E P 1024, .addi E E 1024]

/-- The table of `V₀ … V₁₂₇`. -/
def table : Prog isa :=
  .seq (.block tabInit) (.loop (.block tabBody) (.ne P E))

/-! ## The multiplication -/

/-- Bit `k` (from the left) of the top byte of `x`: `Z := Z ⊕ (Vᵢ ∧ M)`,
with `M` all ones exactly when the bit is set, and `Vᵢ` entry `k` at `P`. -/
def mulStep (k : Nat) : List Instr :=
  [.shift .sll .d M X0 k, .shift .sra .d M M 63,
   .load .d U0 P (16 * k), .load .d U1 P (16 * k + 8),
   .logic .and U0 U0 M, .logic .and U1 U1 M,
   .logic .xor Z0 Z0 U0, .logic .xor Z1 Z1 U1]

/-- The top byte of `x`, `x` shifted left by a byte, and the pointer
advanced. -/
def mulBody : List Instr :=
  (List.range 8).flatMap mulStep ++
    [.shift .sll .d X0 X0 8, .shift .srl .d T X1 56, .logic .or X0 X0 T, .shift .sll .d X1 X1 8,
     .addi P P 128]

/-- `x := Y ⊕ X` for the block `X` at `data`, and `Z := 0`. -/
def blockInit : List Instr :=
  loadBE64 X0 T DP 0 ++ loadBE64 X1 T DP 8 ++
    [.logic .xor X0 X0 Z0, .logic .xor X1 X1 Z1, .li Z0 0, .li Z1 0, .addSp P 0]

/-- One block: `Y := (Y ⊕ X) • H`, and the next block. -/
def block : Prog isa :=
  .seq (.block blockInit)
    (.seq (.loop (.block mulBody) (.ne P E)) (.block [.addi DP DP 16, .addi N N (-1)]))

/-! ## The function -/

/-- `Y` into `Z`. -/
def loadY : List Instr := loadBE64 Z0 T YP 0 ++ loadBE64 Z1 T YP 8

/-- `Z` back to `y`. -/
def storeY : List Instr := storeBE 8 Z0 T YP 0 ++ storeBE 8 Z1 T YP 8

/-- The frame's body: the table, the blocks, `Y` back, and the table zeroed. -/
def body : Prog isa :=
  .seq table
    (.seq (.block loadY)
      (.seq (.loop block (.nonzero N))
        (.seq (.block storeY) (.block (Impl.StackScratch.RISCV64.wipe 256)))))

def ghash : Prog isa :=
  .ite (.zero N) (.block []) (.frame (.alloc 2048) body (.free 2048))

end VG.Impl.Gcm.RISCV64
