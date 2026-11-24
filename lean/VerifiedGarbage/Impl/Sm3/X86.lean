module

public import VerifiedGarbage.Spec.Sm3
public import VerifiedGarbage.TCB.X86.Isa

/-!
# SM3 compression function: x86 (32-bit) implementation

`vg_sm3_compress(state, blocks, n, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

* `esi` points to the scratch buffer and, between blocks, `edi` to the
  current block and `ebp` counts the blocks left; the state pointer is read
  from its argument slot when needed. These, and `esp`, are public; no
  address and no branch depends on anything else.
* `scratch[0..64)` is the 16-word message-expansion window. A block is
  copied into it (big-endian words) first, and `edi` and `ebp` are then
  kept in `scratch[84..92)` during the iterations, which use all six other
  registers. Iteration `j` computes `W_{j+7}` (for `9 ≤ j ≤ 60`), then
  reads `W_j` and `W_{j+4}`.
* The registers `A`, `B`, `E` and `F` are in registers, which are renamed
  between the unrolled iterations with the two temporaries: in iteration
  `j`, `A` is in `ra j`, `B` in `rb j`, `E` in `re j`, `F` in `rf j`, and
  `rx j` and `ry j` are free. `C` and `D` alternate between `scratch[64..72)`
  (`cd`), and `G` and `H` rotate through `scratch[72..84)` (`gh`): an
  iteration writes `B <<< 9` (the next `C`) over `D`, and `F <<< 19` (the
  next `G`) to the third of those words.
* `scratch[96..112)` holds the saved `ebx`, `esi`, `edi`, `ebp`.
-/

@[expose] public section

namespace VG.Impl.Sm3.X86

open VG.X86

/-- The offset of `W[i mod 16]`. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[esi + d]` -/
def sc (d : Nat) : Src := .mem (at_ .esi d)

/-- The registers of `A`, the first temporary and `B`, which follow each
other from one iteration to the next. -/
def abx (k : Nat) : Reg := if k % 3 = 0 then .eax else if k % 3 = 1 then .ebp else .ebx

/-- The registers of `E`, the second temporary and `F`. -/
def efy (k : Nat) : Reg := if k % 3 = 0 then .ecx else if k % 3 = 1 then .edi else .edx

/-- The registers of `A`, `B`, `E`, `F` and the temporaries in iteration `j`. -/
def ra (j : Nat) : Reg := abx j
def rb (j : Nat) : Reg := abx (j + 2)
def rx (j : Nat) : Reg := abx (j + 1)
def re (j : Nat) : Reg := efy j
def rf (j : Nat) : Reg := efy (j + 2)
def ry (j : Nat) : Reg := efy (j + 1)

/-- The two words of `C` and `D`: in iteration `j`, `C` is at `cd (j + 1)`
and `D` at `cd j`. -/
def cd (k : Nat) : Nat := 64 + 4 * (k % 2)

/-- The three words of `G` and `H`: in iteration `j`, `G` is at
`gh (j + 1)`, `H` at `gh j`, and `gh (j + 2)` is free. -/
def gh (k : Nat) : Nat := 72 + 4 * (k % 3)

/-- Where `edi` (the block) and `ebp` (the count) are during the iterations. -/
def spilled : List (Reg × Nat) := [(.edi, 84), (.ebp, 88)]

/-- Copy word `i` of the block (big-endian) to the window. -/
def copyWord (i : Nat) : List Instr := [
  .mov .eax (.mem (at_ .edi (4 * i))),
  .bswap .eax,
  .store (at_ .esi (slot i)) .eax]

/-- Compute `W_i` into its slot, for `16 ≤ i`, with the temporaries `x` and `y`:
`W_i = P_1(W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)) xor (W_{i-13} <<< 7) xor W_{i-6}`. -/
def expand (x y : Reg) (i : Nat) : List Instr := [
  -- x := W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)
  .mov x (sc (slot i)),
  .alu .xor x (sc (slot (i + 7))),
  .mov y (sc (slot (i + 13))),
  .shift .ror y 17,
  .alu .xor x (.reg y),
  -- x := P_1(x) = x xor (x <<< 15) xor (x <<< 23)
  .mov y (.reg x),
  .shift .ror y 17,
  .alu .xor x (.reg y),
  .shift .ror y 24,
  .alu .xor x (.reg y),
  -- x := x xor (W_{i-13} <<< 7) xor W_{i-6}
  .mov y (sc (slot (i + 3))),
  .shift .ror y 25,
  .alu .xor x (.reg y),
  .alu .xor x (sc (slot (i + 10))),
  .store (at_ .esi (slot i)) x]

/-- `T_j <<< (j mod 32)`, an immediate. -/
def tj (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- An iteration, with `W_j` at `w` and `W_{j+4}` at `w₄`, `A`, `B`, `E`, `F` in
the registers `a`, `b`, `e`, `f`, and `C`, `D`, `G`, `H` at `c`, `d`, `g`, `h`:
the new `A` is left in `x`, the new `E` in `y`, the new `C` at `d` and the
new `G` at `n`; `b` and `f` are free after it. -/
def roundAt (lo : Bool) (t : BitVec 32) (w w₄ : Nat) (a b e f x y : Reg) (c d g h n : Nat) :
    List Instr :=
  [ -- x := W'_j + D, W'_j = W_j xor W_{j+4}
    .mov x (sc w),
    .alu .xor x (sc w₄),
    .alu .add x (sc d)] ++
  -- y := FF_j(A, B, C)
  (if lo then [
    .mov y (.reg a),
    .alu .xor y (.reg b),
    .alu .xor y (sc c)]
   else [
    -- ((C xor B) and (B xor A)) xor B
    .mov y (sc c),
    .alu .xor y (.reg b),
    .alu .xor b (.reg a),
    .alu .and y (.reg b),
    .alu .xor b (.reg a),
    .alu .xor y (.reg b)] : List Instr) ++
  [ .alu .add x (.reg y),
    -- C' := B <<< 9, over D
    .shift .ror b 23,
    .store (at_ .esi d) b,
    -- b := A <<< 12; y := SS1 = ((A <<< 12) + (T_j <<< j) + E) <<< 7
    .mov b (.reg a),
    .shift .ror b 20,
    .mov y (.reg b),
    .alu .add y (.imm t),
    .alu .add y (.reg e),
    .shift .ror y 25,
    -- x := x + SS2, SS2 = (A <<< 12) xor SS1: TT1, the new A
    .alu .xor b (.reg y),
    .alu .add x (.reg b),
    -- b := F xor G; G' := F <<< 19; f := H + W_j
    .mov b (.reg f),
    .alu .xor b (sc g),
    .shift .ror f 13,
    .store (at_ .esi n) f,
    .mov f (sc h),
    .alu .add f (sc w)] ++
  -- b := GG_j(E, F, G)
  (if lo then [
    .alu .xor b (.reg e)]
   else [
    -- ((F xor G) and E) xor G
    .alu .and b (.reg e),
    .alu .xor b (sc g)] : List Instr) ++
  [ -- y := TT2 = SS1 + (H + W_j) + GG_j
    .alu .add y (.reg f),
    .alu .add y (.reg b),
    -- y := P_0(TT2) = TT2 xor (TT2 <<< 9) xor (TT2 <<< 17), the new E
    .mov b (.reg y),
    .shift .ror b 23,
    .alu .xor y (.reg b),
    .shift .ror b 24,
    .alu .xor y (.reg b)]

/-- Iteration `j`, with `W_j` and `W_{j+4}` in their slots. -/
def round (j : Nat) : List Instr :=
  roundAt (decide (j < 16)) (tj j) (slot j) (slot (j + 4)) (ra j) (rb j) (re j) (rf j) (rx j) (ry j)
    (cd (j + 1)) (cd j) (gh (j + 1)) (gh j) (gh (j + 2))

/-- What iteration `j` computes of the message expansion first: `W_{j+7}`,
three iterations before the first that reads it. -/
def ahead (j : Nat) : List Instr :=
  if 9 ≤ j ∧ j ≤ 60 then expand (rx j) (ry j) (j + 7) else []

/-- Iterations `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (ahead n ++ round n))

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

/-- Copy the block into the window. -/
def copy : List Instr := (List.range 16).flatMap copyWord

/-- Keep the block pointer and the count in the scratch buffer. -/
def spill : List Instr := spilled.map fun (r, d) => .store (at_ .esi d) r

/-- Whether register `k` (`A = 0, …, H = 7`) is in a register: `A`, `B`, `E`, `F`. -/
def inReg (k : Nat) : Bool := k % 4 < 2

/-- The register of register `k` in iteration `j`, for `A`, `B`, `E` and `F`. -/
def regOf (j k : Nat) : Reg :=
  if k = 0 then ra j else if k = 1 then rb j else if k = 4 then re j else rf j

/-- The offset of register `k` in iteration `j`, for `C`, `D`, `G` and `H`. -/
def offOf (j k : Nat) : Nat :=
  if k = 2 then cd (j + 1) else if k = 3 then cd j else if k = 6 then gh (j + 1) else gh j

/-- Copy the hash value into `A … H`: `C`, `D`, `G`, `H` first, through `eax`,
with the pointer in `edi` (which is none of the registers of `A`, `B`, `E`, `F`
in iteration 0). -/
def load : List Instr :=
  .mov .edi (.mem (at_ .esp 4)) ::
  ([2, 3, 6, 7].flatMap fun k =>
    ([.mov .eax (.mem (at_ .edi (4 * k))), .store (at_ .esi (offOf 0 k)) .eax] : List Instr)) ++
  ([0, 1, 4, 5].map fun k => .mov (regOf 0 k) (.mem (at_ .edi (4 * k))))

/-- `V_{i+1} = (A || … || H) xor V_i`, after the 64 iterations, with the
pointer and a word in the free registers. -/
def update : List Instr :=
  .mov (rx 64) (.mem (at_ .esp 4)) ::
  (List.range 8).flatMap fun k =>
    if inReg k then [
      .alu .xor (regOf 64 k) (.mem (at_ (rx 64) (4 * k))),
      .store (at_ (rx 64) (4 * k)) (regOf 64 k)]
    else [
      .mov (ry 64) (sc (offOf 64 k)),
      .alu .xor (ry 64) (.mem (at_ (rx 64) (4 * k))),
      .store (at_ (rx 64) (4 * k)) (ry 64)]

/-- Take back the block pointer and the count, advance to the next block and
decrement the count (setting ZF when it hits 0). -/
def advance : List Instr :=
  spilled.map (fun (r, d) => .mov r (sc d)) ++
  ([.alu .add .edi (.imm 64), .alu .sub .ebp (.imm 1)] : List Instr)

/-- One block. -/
def body : Prog isa :=
  .seq (.block (copy ++ spill ++ load)) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Sm3.X86
