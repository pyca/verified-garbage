module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

@[expose] public section

namespace VG.Impl.Bignum.RISCV64.Pow57

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64

/-! ## The working space -/

/-- `a7 := A` and `s5 := T`, from array 0's base and the arrays' size. -/
def enter : List Instr :=
  [.shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18), .add .t3 .a7 .s5, .add .t3 .t3 .s5,
    .add .a7 .t3 .t2, .addi .a7 .a7 24, .add .s5 .a7 .t2, .addi .s5 .s5 24]

/-- `t2 :=` the size of `n` limbs. -/
def limbs : List Instr := [.sub .t2 .s5 .a7, .addi .t2 .t2 (-24)]

/-- `enter` undone, and `t0 := w`. -/
def leave : List Instr :=
  limbs ++ [.sub .t3 .a7 .t2, .addi .t3 .t3 (-24), .li .t4 57, .mul .t2 .t2 .t4, .shift .srl .d .t2 .t2 6,
    .addi .s5 .t2 16, .sub .a7 .t3 .s5, .sub .a7 .a7 .s5,
    .shift .srl .d .t0 .s5 3, .addi .t0 .t0 (-2)]

/-! ## Three rows -/

/-- The multipliers `x_i 2⁷`. -/
def rectX : List Instr :=
  [.shift .sll .d .t2 .s2 7, .shift .sll .d .t3 .s3 7, .shift .sll .d .t4 .s4 7]

/-- Three columns, interleaved. -/
def cols : List Instr :=
  [.mul .s0 .s4 .t6, .mul .s1 .s3 .t5, .mulhu .a2 .t3 .t5, .load .d .a3 .a1 0, .load .d .a4 .a0 0,
    .mul .a5 .s2 .a3, .mulhu .a6 .t4 .t6, .add .a2 .a6 .a2, .add .s0 .s0 .s1, .mulhu .s1 .t2 .a3,
    .add .s1 .a2 .s1, .load .d .a2 .a0 8, .mul .a6 .s4 .t5, .shift .sll .d .t0 .s1 57, .add .s0 .s0 .a5,
    .mul .a5 .s3 .a3, .sub .s0 .s0 .t0, .mulhu .t0 .t4 .t5, .add .a4 .a4 .s7, .add .a5 .a6 .a5,
    .load .d .t6 .a1 8, .add .s0 .a4 .s0, .store .d .s0 .a0 0, .mulhu .s0 .t3 .a3, .mulhu .a4 .t2 .t6,
    .mul .a6 .s2 .t6, .add .a5 .a5 .a6, .add .s0 .t0 .s0, .mul .a6 .s4 .a3, .add .s0 .s0 .a4,
    .mulhu .a3 .t4 .a3, .load .d .a4 .a0 16, .shift .sll .d .t0 .s0 57, .sub .a5 .a5 .t0, .mulhu .t0 .t3 .t6,
    .add .s1 .a2 .s1, .mul .a2 .s3 .t6, .add .s1 .s1 .a5, .store .d .s1 .a0 8, .load .d .t5 .a1 16,
    .mulhu .s1 .t2 .t5, .add .a2 .a6 .a2, .add .a3 .a3 .t0, .mul .a5 .s2 .t5, .add .a2 .a2 .a5,
    .add .s7 .a3 .s1, .add .s0 .a4 .s0, .shift .sll .d .s1 .s7 57, .sub .s1 .a2 .s1, .add .s0 .s0 .s1,
    .store .d .s0 .a0 16]

/-- Three rows, up to `a1 = e`. -/
def rect (e : Reg) : Prog isa :=
  .loop (.block (cols ++ ([.addi .a0 .a0 24, .addi .a1 .a1 24] : List Instr))) (.ne .a1 e)

/-! ## The Montgomery reduction -/

/-- `t6 := 2⁵⁷ - 1`. -/
def mask57 : List Instr := [.li .t6 (-1), .shift .srl .d .t6 .t6 7]

/-- `rl`, `rh` := the low 57 bits and the rest of `x y`, for `xp = x 2⁷`; `rl` is below `2⁵⁷`. -/
def mul57 (rl rh x xp y tmp : Reg) : List Instr :=
  [.mulhu rh xp y, .mul rl x y, .shift .sll .d tmp rh 57, .sub rl rl tmp]

/-- `u := v (-m⁻¹) mod 2⁵⁷` and `up := u 2⁷`, and `v :=` the carry of `v + u m`'s column: `v / 2⁵⁷` rounded up, as
the column is a multiple of `2⁵⁷`. -/
def quot (u up v : Reg) : List Instr :=
  [.mul u v .t1, .add v v .t6, .shift .sll .d up u 7, .logic .and u u .t6, .shift .srl .d v v 57]

/-- The three quotients of a block of rows, and what their first three columns carry. -/
def redHead : List Instr :=
  limbs ++ [.sub .t2 .a7 .t2, .addi .a1 .t2 (-24), .load .d .a4 .a1 0, .load .d .a5 .a1 8, .load .d .a6 .a1 16] ++
  mask57 ++
  -- column 0
  ([.load .d .s0 .a0 0] : List Instr) ++ quot .s2 .t2 .s0 ++
  ([.mulhu .a3 .t2 .a4, .load .d .s1 .a0 8, .add .s0 .s0 .a3, .add .s0 .s0 .s1] : List Instr) ++
  -- column 1
  mul57 .a2 .a3 .s2 .t2 .a5 .t0 ++ ([.add .s0 .s0 .a2] : List Instr) ++ quot .s3 .t3 .s0 ++
  ([.mulhu .s1 .t3 .a4, .load .d .t5 .a0 16, .add .s0 .s0 .a3, .add .s0 .s0 .t5, .add .s0 .s0 .s1] : List Instr) ++
  -- column 2
  mul57 .a2 .s7 .s2 .t2 .a6 .t0 ++ ([.add .s0 .s0 .a2] : List Instr) ++ mul57 .a2 .a3 .s3 .t3 .a5 .t0 ++
  ([.add .s0 .s0 .a2, .add .s7 .s7 .a3] : List Instr) ++ quot .s4 .t4 .s0 ++
  ([.mulhu .a3 .t4 .a4, .add .s7 .s7 .s0, .add .s7 .s7 .a3,
    .addi .t5 .a6 0, .addi .t6 .a5 0, .addi .a0 .a0 24, .addi .a1 .a1 24] : List Instr)

/-- The next block's `T`; `t3` where they end. -/
def rowNext : List Instr := limbs ++ [.sub .a0 .a0 .t2, .add .t3 .s5 .t2]

/-- The reduction's rows. -/
def redRows : Prog isa :=
  .seq (.block [.addi .a0 .s5 0])
    (.loop (.seq (.block redHead) (.seq (rect .a7) (.block rowNext))) (.ne .a0 .t3))

/-- A step of a carry pass, from `a0` to `a1`: the carry in `t5`, the mask in `t6`. -/
def normStep (k : Nat) : List Instr :=
  [.load .d .s0 .a0 k, .add .s0 .s0 .t5, .logic .and .s1 .s0 .t6, .shift .srl .d .t5 .s0 57, .store .d .s1 .a1 k]

/-- A carry pass from `a0` to `a1`, up to `a0 = t3`, three limbs at a time. -/
def norm : Prog isa :=
  .seq (.block (mask57 ++ ([.li .t5 0] : List Instr)))
    (.loop (.block ((List.range 3).flatMap (fun k => normStep (8 * k)) ++
      ([.addi .a0 .a0 24, .addi .a1 .a1 24] : List Instr))) (.ne .a0 .t3))

/-- `A := T R'⁻¹ mod m` (below `2 m`). -/
def reduce57 : Prog isa :=
  .seq redRows (.seq (.block (limbs ++ [.add .a0 .s5 .t2, .addi .a1 .a7 0, .add .t3 .a0 .t2])) norm)

/-- `T := 0`. -/
def zeroT57 : Prog isa :=
  .seq (.block (limbs ++ [.shift .sll .d .t2 .t2 1, .add .t4 .s5 .t2, .addi .t3 .s5 0, .li .s0 0]))
    (.loop (.block [.store .d .s0 .t3 0, .store .d .s0 .t3 8, .store .d .s0 .t3 16, .addi .t3 .t3 24]) (.ne .t3 .t4))

/-! ## The product -/

/-- The multipliers of three rows, of `E`, which is after `T`. -/
def mulHead : List Instr :=
  limbs ++ [.shift .sll .d .t2 .t2 1, .add .a2 .a0 .t2, .load .d .s2 .a2 0, .load .d .s3 .a2 8, .load .d .s4 .a2 16] ++
    rectX ++ [.li .t5 0, .li .t6 0, .li .s7 0, .addi .a1 .a7 0]

/-- `T := A E`. -/
def mulRows : Prog isa :=
  .seq (.block [.addi .a0 .s5 0])
    (.loop (.seq (.block mulHead) (.seq (rect .s5) (.block rowNext))) (.ne .a0 .t3))

/-- A carry pass over `T`. -/
def normT : Prog isa :=
  .seq (.block (limbs ++ [.addi .a0 .s5 0, .addi .a1 .s5 0, .shift .sll .d .t2 .t2 1, .add .t3 .a0 .t2])) norm

/-- `A := A E R'⁻¹ mod m`. -/
def mulOp57 : Prog isa :=
  .seq (.block enter) (.seq zeroT57 (.seq mulRows (.seq normT (.seq reduce57 (.block leave)))))

/-! ## The square -/

/-- A block of three rows, at `a7 + t4` and `s5 + 2 t4`: the cross products of its limbs, and the multipliers. -/
def sqrHead : List Instr :=
  [.add .a2 .a7 .t4, .add .a0 .s5 .t4, .add .a0 .a0 .t4, .load .d .s2 .a2 0, .load .d .s3 .a2 8,
    .load .d .s4 .a2 16, .addi .a1 .a2 24] ++ rectX ++
  mul57 .s0 .s1 .s2 .t2 .s3 .t0 ++ mul57 .a2 .a3 .s2 .t2 .s4 .t0 ++ mul57 .a4 .a5 .s3 .t3 .s4 .t0 ++
  [.load .d .t0 .a0 8, .load .d .t5 .a0 16, .load .d .t6 .a0 32, .add .t0 .t0 .s0, .add .t5 .t5 .s1,
    .add .t5 .t5 .a2, .add .s7 .a3 .a4, .add .t6 .t6 .a5, .store .d .t0 .a0 8, .store .d .t5 .a0 16,
    .store .d .t6 .a0 32, .li .t5 0, .li .t6 0, .addi .a0 .a0 24]

/-- The next block's offset into `t4`, the limbs' size in `t2`. -/
def sqrNext : List Instr := limbs ++ [.sub .t4 .a0 .s5, .sub .t4 .t4 .t2]

/-- `T :=` the cross products of `A`. -/
def sqrRows : Prog isa :=
  .seq (.block [.li .t4 0])
    (.loop (.seq (.block sqrHead) (.seq (rect .s5) (.block sqrNext))) (.ne .t4 .t2))

/-- Columns `2 i` and `2 i + 1` of `2 T + Σ aᵢ² 2^(114 i)`, with the carry `t5`. -/
def diagStep57 : List Instr :=
  [.load .d .s2 .a1 0] ++ [.shift .sll .d .t2 .s2 7] ++ mul57 .s0 .s1 .s2 .t2 .s2 .a2 ++
  [.load .d .a3 .a0 0, .load .d .a4 .a0 8, .shift .sll .d .a3 .a3 1, .shift .sll .d .a4 .a4 1,
    .add .a3 .a3 .t5, .add .a3 .a3 .s0, .logic .and .a5 .a3 .t6, .shift .srl .d .t5 .a3 57,
    .store .d .a5 .a0 0, .add .a4 .a4 .s1, .add .a4 .a4 .t5, .logic .and .a5 .a4 .t6,
    .shift .srl .d .t5 .a4 57, .store .d .a5 .a0 8]

def diag57 : Prog isa :=
  .seq (.block (mask57 ++ ([.li .t5 0, .addi .a0 .s5 0] : List Instr) ++ limbs ++ [.addi .a1 .a7 0, .add .t3 .a7 .t2]))
    (.loop (.block (diagStep57 ++ ([.addi .a0 .a0 16, .addi .a1 .a1 8] : List Instr))) (.ne .a1 .t3))

/-- `A := A² R'⁻¹ mod m`. -/
def sqrOp57 : Prog isa :=
  .seq (.block enter) (.seq zeroT57 (.seq sqrRows (.seq diag57 (.seq reduce57 (.block leave)))))

/-! ## Between the radices -/

/-- The `t5` limbs at `t4` of the number at `t3`, whose word `w` is 0. -/
def unpack : Prog isa :=
  .seq (.block [.li .s4 (-1), .shift .srl .d .s4 .s4 7, .li .t2 0])
    (countLoop .t5 [.shift .srl .d .s0 .t2 6, .shift .sll .d .s0 .s0 3, .add .s0 .s0 .t3, .load .d .s1 .s0 0,
      .load .d .s2 .s0 8, .shiftReg .srl .d .s1 .s1 .t2, .logicImm .xor .s3 .t2 (-1), .shift .sll .d .s2 .s2 1,
      .shiftReg .sll .d .s2 .s2 .s3, .add .s1 .s1 .s2, .logic .and .s1 .s1 .s4, .store .d .s1 .t4 0,
      .addi .t4 .t4 8, .addi .t2 .t2 57])

/-- `unpack` from array 5, its word `w` zeroed. -/
def unpackFrom (dst : List Instr) : Prog isa :=
  .seq (.block ([.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .add .t5 .t3 .s5, .addi .t5 .t5 (-16),
    .li .s0 0, .store .d .s0 .t5 0, .shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18),
    .shift .srl .d .t5 .t2 3] ++ dst)) unpack

/-- `t4 := M`. -/
def atM : List Instr := [.add .t4 .a7 .s5, .add .t4 .t4 .s5]
/-- `t4 := A`. -/
def atA : List Instr := atM ++ [.add .t4 .t4 .t2, .addi .t4 .t4 24]
/-- `t4 := E`. -/
def atE : List Instr := atA ++ [.add .t4 .t4 .t2, .addi .t4 .t4 24, .add .t4 .t4 .t2, .add .t4 .t4 .t2]

/-- The padding after `M` and after `A`, from `t2`, `t4` as `unpackFrom atM` leaves them… -/
def pads : List Instr :=
  [.add .t4 .a7 .s5, .add .t4 .t4 .s5, .shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18), .li .s0 0,
    .add .t4 .t4 .t2, .store .d .s0 .t4 0, .store .d .s0 .t4 8, .store .d .s0 .t4 16, .add .t4 .t4 .t2,
    .store .d .s0 .t4 24, .store .d .s0 .t4 32, .store .d .s0 .t4 40]

/-- `A`, packed into array 6: word `j` from bit `64 j`, that is bit `sh` of limb `64 j / 57`. -/
def pack : Prog isa :=
  .seq (.block ([.shift .srl .d .t2 .s5 3, .add .t2 .t2 .s5, .addi .t2 .t2 (-18)] ++ atA ++
      [.shift .sll .d .t3 .s5 2, .add .t3 .t3 .s5, .add .t3 .t3 .s5, .add .t3 .t3 .a7, .li .t6 0, .li .s4 57,
      .li .a2 1150, .addi .t5 .t0 0]))
    (countLoop .t5 [.mul .a3 .t6 .a2, .shift .srl .d .a3 .a3 16, .mul .a4 .a3 .s4, .sub .a4 .t6 .a4, .sub .a5 .s4 .a4,
      .shift .sll .d .a3 .a3 3, .add .a3 .a3 .t4, .load .d .s1 .a3 0, .load .d .s2 .a3 8, .load .d .s3 .a3 16,
      .shiftReg .srl .d .s1 .s1 .a4, .shiftReg .sll .d .s2 .s2 .a5, .shift .sll .d .s3 .s3 57,
      .shiftReg .sll .d .s3 .s3 .a5, .add .s1 .s1 .s2, .add .s1 .s1 .s3, .store .d .s1 .t3 0,
      .addi .t3 .t3 8, .addi .t6 .t6 64])

end VG.Impl.Bignum.RISCV64.Pow57
