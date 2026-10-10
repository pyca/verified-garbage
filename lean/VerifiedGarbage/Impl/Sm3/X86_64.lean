import VerifiedGarbage.Spec.Sm3
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# SM3 compression function: x86-64 implementation

`vg_sm3_compress(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`.

* The registers `A … H` live in the low 32 bits of eight registers. An
  iteration writes only `TT1` and `P_0(TT2)`, over `D` and `H` (and rotates
  `B` and `F` in place), so the unrolled iterations rename the registers
  rather than move them: `A … D` rotate through `group₁`, `E … H` through
  `group₂`, and in iteration `j`, register `k` is in `var j k`.
* The message expansion is kept as a 16-word window `W[i mod 16]` in
  `scratch[0..64)`: iteration `j` computes `W_{j+4}` (from the block while
  `j + 4 < 16`), then reads `W_j` and `W_{j+4}` for `W_j` and `W'_j`.
* `rbx, rbp, r12–r15` are saved in `scratch[64..112)` and restored on exit.
* Rotations left are rotations right by the complement (`ror`).
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Sm3.X86_64

open VG.X86_64

/-- The registers holding `A … D`. -/
def group₁ : List Reg := [.rax, .rbx, .rbp, .r8]

/-- The registers holding `E … H`. -/
def group₂ : List Reg := [.r9, .r10, .r11, .r12]

/-- The register holding register `k` (`A = 0, …, H = 7`) at the start of
iteration `j`. -/
def var (j k : Nat) : Reg :=
  if k < 4 then group₁.getD ((k + 4 - j % 4) % 4) .rax
  else group₂.getD ((k + 4 - j % 4) % 4) .rax

/-- Temporaries. -/
def T0 : Reg := .r13
def T1 : Reg := .r14
def T2 : Reg := .r15

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : MemOp := at_ .rcx (4 * (i % 16))

/-- Compute `W_i` into its slot:
`W_i = P_1(W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)) xor (W_{i-13} <<< 7) xor W_{i-6}`
for `i ≥ 16`, word `i` of the block (big-endian) before. -/
def expand (i : Nat) : List Instr :=
  if i < 16 then [
    .mov32 T0 (.mem (at_ .rsi (4 * i))),
    .bswap32 T0,
    .store32 (slot i) T0]
  else [
    -- T0 := W_{i-16} xor W_{i-9} xor (W_{i-3} <<< 15)
    .mov32 T0 (.mem (slot i)),
    .alu32 .xor T0 (.mem (slot (i + 7))),
    .mov32 T1 (.mem (slot (i + 13))),
    .shift32 .ror T1 17,
    .alu32 .xor T0 (.reg T1),
    -- T0 := P_1(T0)
    .mov32 T1 (.reg T0),
    .shift32 .ror T1 17,
    .mov32 T2 (.reg T0),
    .shift32 .ror T2 9,
    .alu32 .xor T0 (.reg T1),
    .alu32 .xor T0 (.reg T2),
    -- T0 := T0 xor (W_{i-13} <<< 7) xor W_{i-6}
    .mov32 T1 (.mem (slot (i + 3))),
    .shift32 .ror T1 25,
    .alu32 .xor T0 (.reg T1),
    .alu32 .xor T0 (.mem (slot (i + 10))),
    .store32 (slot i) T0]

/-- `T_j <<< (j mod 32)`, an immediate. -/
def tj (j : Nat) : BitVec 32 := (Spec.Sm3.T j).rotateLeft (j % 32)

/-- Iteration `j`, with `W_j` and `W_{j+4}` in their slots. -/
def round (j : Nat) : List Instr :=
  let a := var j 0; let b := var j 1; let c := var j 2; let d := var j 3
  let e := var j 4; let f := var j 5; let g := var j 6; let h := var j 7
  [ -- T0 := A <<< 12; T1 := SS1 = ((A <<< 12) + E + (T_j <<< j)) <<< 7
    .mov32 T0 (.reg a),
    .shift32 .ror T0 20,
    .mov32 T1 (.reg T0),
    .alu32 .add T1 (.reg e),
    .alu32 .add T1 (.imm (tj j)),
    .shift32 .ror T1 25,
    -- h := H + SS1
    .alu32 .add h (.reg T1),
    -- d := D + SS2, SS2 = SS1 xor (A <<< 12)
    .alu32 .xor T0 (.reg T1),
    .alu32 .add d (.reg T0),
    -- h := h + W_j; d := d + W'_j, W'_j = W_j xor W_{j+4}
    .alu32 .add h (.mem (slot j)),
    .mov32 T0 (.mem (slot j)),
    .alu32 .xor T0 (.mem (slot (j + 4))),
    .alu32 .add d (.reg T0)] ++
  -- d := d + FF_j(A, B, C), which is TT1
  (if j < 16 then [
    .mov32 T0 (.reg a),
    .alu32 .xor T0 (.reg b),
    .alu32 .xor T0 (.reg c)]
   else [
    -- (A or B) and C or (A and B)
    .mov32 T0 (.reg a),
    .alu32 .or T0 (.reg b),
    .alu32 .and T0 (.reg c),
    .mov32 T1 (.reg a),
    .alu32 .and T1 (.reg b),
    .alu32 .or T0 (.reg T1)] : List Instr) ++
  [.alu32 .add d (.reg T0)] ++
  -- h := h + GG_j(E, F, G), which is TT2
  (if j < 16 then [
    .mov32 T0 (.reg e),
    .alu32 .xor T0 (.reg f),
    .alu32 .xor T0 (.reg g)]
   else [
    -- (F xor G) and E xor G
    .mov32 T0 (.reg f),
    .alu32 .xor T0 (.reg g),
    .alu32 .and T0 (.reg e),
    .alu32 .xor T0 (.reg g)] : List Instr) ++
  [ .alu32 .add h (.reg T0),
    -- C' := B <<< 9; G' := F <<< 19
    .shift32 .ror b 23,
    .shift32 .ror f 13,
    -- h := P_0(TT2) = TT2 xor (TT2 <<< 9) xor (TT2 <<< 17)
    .mov32 T0 (.reg h),
    .shift32 .ror T0 23,
    .mov32 T1 (.reg h),
    .shift32 .ror T1 15,
    .alu32 .xor h (.reg T0),
    .alu32 .xor h (.reg T1)]

/-- `W_0 … W_3`, then iterations `0 … n-1`, each computing `W_{j+4}` first. -/
def rounds : Nat → Prog isa
  | 0 => .block (expand 0 ++ expand 1 ++ expand 2 ++ expand 3)
  | n + 1 => .seq (rounds n) (.block (expand (n + 4) ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.rbx, 64), (.rbp, 72), (.r12, 80), (.r13, 88), (.r14, 96), (.r15, 104)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rcx d))

/-- Load the hash value (`64 % 4 = 0`, so the registers are in the same
places after the 64 iterations). -/
def load : List Instr := (List.range 8).map fun k => .mov32 (var 0 k) (.mem (at_ .rdi (4 * k)))

/-- `V_{i+1} = (A || … || H) xor V_i`. -/
def update : List Instr :=
  (List.range 8).map (fun k => .alu32 .xor (var 0 k) (.mem (at_ .rdi (4 * k)))) ++
  (List.range 8).map (fun k => .store32 (at_ .rdi (4 * k)) (var 0 k))

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr := [.alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sm3.X86_64
