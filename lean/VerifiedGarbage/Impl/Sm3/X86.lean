import VerifiedGarbage.Spec.Sm3
import VerifiedGarbage.TCB.X86.Isa

/-!
# SM3 compression function: x86 (32-bit) implementation

`vg_sm3_compress(state, blocks, n, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

With only seven usable registers, the registers `A … H` live in memory:
* `esi` points to the scratch buffer, `edi` to the current block, and `ebp`
  counts the blocks left; the state pointer is read from its argument slot
  when needed. These, and `esp`, are public; no address and no branch
  depends on anything else.
* `scratch[0..64)` is the 16-word message-expansion window: iteration `j`
  computes `W_{j+4}` (from the block while `j + 4 < 16`), then reads `W_j`
  and `W_{j+4}`. `scratch[64..96)` holds `A … H`, renamed between the
  unrolled iterations: `A … D` rotate through `scratch[64..80)`, `E … H`
  through `scratch[80..96)`, and in iteration `j`, register `k` is at offset
  `var j k`. `scratch[96..112)` holds the saved `ebx`, `esi`, `edi`, `ebp`.
* `eax`, `ebx`, `ecx`, `edx` are the temporaries. An iteration reads the
  window before it stores anything.
-/

namespace VG.Impl.Sm3.X86

open VG.X86

/-- The offset of register `k` (`A = 0, …, H = 7`) at the start of iteration `j`. -/
def var (j k : Nat) : Nat :=
  if k < 4 then 64 + 4 * ((k + 4 - j % 4) % 4) else 80 + 4 * ((k + 4 - j % 4) % 4)

/-- The offset of `W[i mod 16]`. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[esi + d]` -/
def sc (d : Nat) : Src := .mem (at_ .esi d)

/-- Compute `W_i` into its slot:
`W_i = P_1(W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)) xor (W_{i-13} <<< 7) xor W_{i-6}`
for `i ≥ 16`, word `i` of the block (big-endian) before. -/
def expand (i : Nat) : List Instr :=
  if i < 16 then [
    .mov .eax (.mem (at_ .edi (4 * i))),
    .bswap .eax,
    .store (at_ .esi (slot i)) .eax]
  else [
    -- eax := W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)
    .mov .eax (sc (slot i)),
    .alu .xor .eax (sc (slot (i + 7))),
    .mov .ebx (sc (slot (i + 13))),
    .shift .ror .ebx 17,
    .alu .xor .eax (.reg .ebx),
    -- eax := P_1(eax)
    .mov .ebx (.reg .eax),
    .shift .ror .ebx 17,
    .mov .ecx (.reg .eax),
    .shift .ror .ecx 9,
    .alu .xor .eax (.reg .ebx),
    .alu .xor .eax (.reg .ecx),
    -- eax := eax xor (W_{i-13} <<< 7) xor W_{i-6}
    .mov .ebx (sc (slot (i + 3))),
    .shift .ror .ebx 25,
    .alu .xor .eax (.reg .ebx),
    .alu .xor .eax (sc (slot (i + 10))),
    .store (at_ .esi (slot i)) .eax]

/-- `T_j <<< (j mod 32)`, an immediate. -/
def tj (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- Iteration `j`, with `W_j` and `W_{j+4}` in their slots. -/
def round (j : Nat) : List Instr :=
  let a := var j 0; let b := var j 1; let c := var j 2; let d := var j 3
  let e := var j 4; let f := var j 5; let g := var j 6; let h := var j 7
  [ -- eax := A <<< 12; ebx := SS1 = ((A <<< 12) + E + (T_j <<< j)) <<< 7
    .mov .eax (sc a),
    .shift .ror .eax 20,
    .mov .ebx (.reg .eax),
    .alu .add .ebx (sc e),
    .alu .add .ebx (.imm (tj j)),
    .shift .ror .ebx 25,
    -- eax := SS2 = (A <<< 12) xor SS1
    .alu .xor .eax (.reg .ebx),
    -- edx := H + SS1 + W_j
    .mov .edx (sc h),
    .alu .add .edx (.reg .ebx),
    .alu .add .edx (sc (slot j)),
    -- ecx := D + SS2 + W'_j, W'_j = W_j xor W_{j+4}
    .mov .ecx (sc d),
    .alu .add .ecx (.reg .eax),
    .mov .eax (sc (slot j)),
    .alu .xor .eax (sc (slot (j + 4))),
    .alu .add .ecx (.reg .eax)] ++
  -- ecx := ecx + FF_j(A, B, C), which is TT1, the new A (over D)
  (if j < 16 then [
    .mov .eax (sc a),
    .alu .xor .eax (sc b),
    .alu .xor .eax (sc c)]
   else [
    -- (A or B) and C or (A and B)
    .mov .eax (sc a),
    .alu .or .eax (sc b),
    .alu .and .eax (sc c),
    .mov .ebx (sc a),
    .alu .and .ebx (sc b),
    .alu .or .eax (.reg .ebx)] : List Instr) ++
  [.alu .add .ecx (.reg .eax), .store (at_ .esi d) .ecx] ++
  -- edx := edx + GG_j(E, F, G), which is TT2
  (if j < 16 then [
    .mov .eax (sc e),
    .alu .xor .eax (sc f),
    .alu .xor .eax (sc g)]
   else [
    -- (F xor G) and E xor G
    .mov .eax (sc f),
    .alu .xor .eax (sc g),
    .alu .and .eax (sc e),
    .alu .xor .eax (sc g)] : List Instr) ++
  [ .alu .add .edx (.reg .eax),
    -- The new E (over H) := P_0(TT2) = TT2 xor (TT2 <<< 9) xor (TT2 <<< 17)
    .mov .eax (.reg .edx),
    .shift .ror .eax 23,
    .mov .ebx (.reg .edx),
    .shift .ror .ebx 15,
    .alu .xor .edx (.reg .eax),
    .alu .xor .edx (.reg .ebx),
    .store (at_ .esi h) .edx,
    -- C' := B <<< 9; G' := F <<< 19
    .mov .eax (sc b),
    .shift .ror .eax 23,
    .store (at_ .esi b) .eax,
    .mov .eax (sc f),
    .shift .ror .eax 13,
    .store (at_ .esi f) .eax]

/-- `W_0 … W_3`, then iterations `0 … n-1`, each computing `W_{j+4}` first. -/
def rounds : Nat → Prog isa
  | 0 => .block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)
  | n + 1 => .seq (rounds n) (.block (expand (n + 4) ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 96), (.esi, 100), (.edi, 104), (.ebp, 108)]

/-- Save the callee-saved registers, load the arguments, and set ZF if there
are no blocks. -/
def prologue : List Instr :=
  ([.mov .eax (.mem (at_ .esp 16))] : List Instr) ++
  saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  ([.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12)),
   .alu .test .ebp (.reg .ebp)] : List Instr)

/-- Restore the callee-saved registers (`esi`, the base, last). -/
def epilogue : List Instr :=
  [.mov .ebx (sc 96), .mov .edi (sc 104), .mov .ebp (sc 108), .mov .esi (sc 100)]

/-- Copy the hash value into `A … H` (`64 % 4 = 0`, so they are in the same
place after the 64 iterations). -/
def load : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) ::
  (List.range 8).flatMap fun k => [.mov .ebx (.mem (at_ .eax (4 * k))), .store (at_ .esi (var 0 k)) .ebx]

/-- `V_{i+1} = (A || … || H) xor V_i`. -/
def update : List Instr :=
  .mov .eax (.mem (at_ .esp 4)) ::
  (List.range 8).flatMap fun k => [
    .mov .ebx (sc (var 0 k)),
    .alu .xor .ebx (.mem (at_ .eax (4 * k))),
    .store (at_ .eax (4 * k)) .ebx]

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .edi (.imm 64), .alu .sub .ebp (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Sm3.X86
