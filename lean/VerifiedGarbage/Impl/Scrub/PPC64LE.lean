module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Returning without secret residue (64-bit little-endian PowerPC)

`scrub retBits depth c` runs `c`, then clears everything `c` may have left
where its Rust caller cannot clear it (`PPC64LE.NoResidue`), as
`Impl/Scrub/X86_64.lean` and `Impl/Scrub/RISCV64.lean` do:

* the stack below the stack pointer that `c`'s frames may have written: of
  the `depth` bytes its frames use at most, all but the bottom 32 (a frame's
  region starts 32 bytes above its stack pointer, past the header of the
  ELFv2 minimum frame, which no frame makes writable: see `push` in
  `TCB/PPC64LE/Isa.lean`). The clearing's own frames have such headers too,
  so it wipes the stack in nested levels of the sizes `cs` (`wipe`): at every
  level but the last, a frame of `c + 32` bytes, whose region is the `c`
  bytes below the stack pointer, where the header of the next level's
  frame will be, then a frame of `c` bytes, inside which the next levels run;
  the last level is one frame of `c` bytes, whose header is the bottom 32
  bytes. Each frame's region is zeroed, from its base up, by `std r0, 8k(r12)`
  with `r0` zero and `r12` the region's base (`addi r12, r1, 32`);
* the volatile registers (ELFv2 ABI §2.2.2.1, Table 2.21): `r0` and `r4`–
  `r12` with `li r, 0`, the bits of `r3`, the result, above its `retBits` low
  ones, `XER`'s carry bit CA with `addc r0, r0, r0` (of zeros, which carries
  nothing), and `v0`–`v19` with `vxor v, v, v`.

The model has no other register a function may change (see
`TCB/PPC64LE/Residue.lean`).
-/

@[expose] public section

namespace VG.Impl.Scrub.PPC64LE

open VG.PPC64LE

/-- `li r, 0`. -/
def zeroR (r : Reg) : Instr := .li r 0

/-- `vxor v, v, v`. -/
def zeroV (v : VReg) : Instr := .vop (.logic .xor v v v)

/-- The volatile registers but `r0` and `r3`. -/
def scratchRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The vector registers, all volatile. -/
def vregs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9,
   .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18, .v19]

/-- Clear the bits of `r3` above a result of `retBits` bits: all of them
(`li`), or, for a narrower result, by a shift left then right of the same
amount. -/
def retFix (retBits : Nat) : List Instr :=
  if retBits = 0 then [zeroR .r3]
  else if retBits < 64 then [.lsl .r3 .r3 (64 - retBits), .lsr .d .r3 .r3 (64 - retBits)]
  else []

/-- `std r0, 8k(r12)` for `k` from `k₀` to `k₀ + n - 1`. -/
def stores (k₀ : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => .store .d .r0 .r12 (8 * k₀) :: stores (k₀ + 1) n

/-- A frame of `b` bytes whose region, the `b - 32` bytes below the stack
pointer, it zeroes. -/
def wipeFrame (b : Nat) : Prog isa :=
  .frame (.alloc b) (.block (.addSp .r12 32 :: stores 0 ((b - 32) / 8))) (.free b)

/-- Zero the stack below `r1` in levels of the sizes `cs` (see the module
docs). -/
def wipe : List Nat → Prog isa
  | [] => .block []
  | [c] => wipeFrame c
  | c :: c' :: cs => .seq (wipeFrame (c + 32)) (.frame (.alloc c) (wipe (c' :: cs)) (.free c))

/-- Levels summing to `n`, at most `fuel` of them: each at most 4048 bytes
(so that the frame of 32 bytes more is less than 4096), and each but the
first at least 64 (so that it zeroes the header the level above left). -/
def chunksAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 =>
    if n + 1 ≤ 4048 then [n + 1]
    else if 4032 + 64 ≤ n + 1 then 4032 :: chunksAux f (n + 1 - 4032)
    else 3968 :: chunksAux f (n + 1 - 3968)

def chunks (n : Nat) : List Nat := chunksAux (n / 3968 + 1) n

/-- The clearing: `r0` zeroed, the stack in levels of the sizes `cs`, then
the result's upper bits, the scratch registers, CA and the vector
registers. -/
def scrubTail (retBits : Nat) (cs : List Nat) : Prog isa :=
  .seq (.block [zeroR .r0]) (.seq (wipe cs) (.seq (.block (retFix retBits))
    (.seq (.block (scratchRegs.map zeroR)) (.block (.addc .r0 .r0 .r0 :: vregs.map zeroV)))))

/-- `c`, then the clearing of the `depth` bytes of stack its frames use. -/
def scrub (retBits depth : Nat) (c : Prog isa) : Prog isa :=
  .seq c (scrubTail retBits (chunks depth))

end VG.Impl.Scrub.PPC64LE
