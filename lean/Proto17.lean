import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr

/-! Throwaway, unproven: RISC-V Montgomery multiplication by two-row FIOS (rows `i` and
`i + 1` in one pass, the second skewed one word behind), and squaring with a two-row
reduction (rows `i`, `i + 1` added at each word in one load/store). Even `w` only.
Uses `s5`–`s11` freely (the harness saves them). Printed for timing on RISE. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

namespace Proto17

/-! ## Harness (Proto12's) -/

def save : List Instr :=
  (List.range 12).flatMap fun i =>
    [.store .d ([Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11].getD i .s0) .a0 (128 + 8 * i)]
def restore : List Instr :=
  ((List.range 12).filter (· != 6)).flatMap (fun i =>
    [.load .d ([Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11].getD i .s0) .s6 (128 + 8 * i)]) ++
  [.load .d .s6 .s6 (128 + 8 * 6)]
def setup : List Instr :=
  [.addi .s6 .a0 0, .addi .s7 .a2 0, .addi .t0 .a1 0, .shift .sll .d .s5 .a1 3, .addi .s5 .s5 16,
   .addi .a7 .a0 256, .load .d .t1 .a0 56]
def base (rd : Reg) (j : Nat) : List Instr := .addi rd .a7 0 :: List.replicate j (.add rd rd .s5)
def spill : List Instr :=
  [.shift .sll .d .t2 .s5 3, .sub .t2 .t2 .s5, .add .t2 .t2 .a7,
   .store .d .s5 .t2 0, .store .d .s6 .t2 8, .store .d .s7 .t2 16]
def check : List Instr :=
  [.shift .sll .d .t3 .t0 3, .addi .t3 .t3 16, .shift .sll .d .t4 .t3 3, .sub .t4 .t4 .t3,
   .add .t4 .t4 .a7, .sub .t2 .a6 .a5, .store .d .t2 .t4 24, .sub .t2 .a5 .a7,
   .store .d .t2 .t4 32]
def unspill : List Instr :=
  [.shift .sll .d .t2 .t0 3, .addi .t2 .t2 16, .shift .sll .d .t3 .t2 3, .sub .t3 .t3 .t2,
   .add .t2 .t3 .a7, .load .d .s5 .t2 0, .load .d .s6 .t2 8, .load .d .s7 .t2 16,
   .addi .s7 .s7 (-1)]

def mulLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a4 6 ++ base .a5 2 ++ base .a6 3 ++ spill))
      (.seq op (.block (check ++ unspill)))) (.nonzero .s7)) (.block restore))

/-- The square `[a]² R⁻¹` through the multiplication, `b` = `a` (array 5). -/
def sqrByMulLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a4 5 ++ base .a5 2 ++ base .a6 3 ++ spill))
      (.seq op (.block (check ++ unspill)))) (.nonzero .s7)) (.block restore))

def sqrLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a5 2 ++ base .a6 4 ++ spill))
      (.seq op (.block (check ++ unspill)))) (.nonzero .s7)) (.block restore))

/-! ## (A) Two-row FIOS multiplication

Rows `aᵢ` (`t6`, `u` in `t2`, carries `s0`, `s1`) and `aᵢ₊₁` (`s5`, `u` in `s6`, carries
`s7`, `s8`). At step `j`, row `i` makes word `j - 1` of `T'` (kept in `s2`), which row `i + 1`
takes at its step `j - 1`, storing word `j - 2` of `T''`. `bⱼ`, `mⱼ` alternate between
(`a6`, `a7`) and (`s9`, `s10`); the previous pair serves row `i + 1`. -/

/-- `x += p * q` parts: `lo := lo + p q mod 2⁶⁴ + c`, `c := ` the high word with the carries,
through `s3`, `s4`. -/
def mac (lo p q c : Reg) : List Instr :=
  [.mul .s3 p q, .mulhu .s4 p q, .add lo lo .s3, .sltu .s3 lo .s3, .add .s4 .s4 .s3,
    .add lo lo c, .sltu c lo c, .add c .s4 c]

/-- Row `i`'s step at `j` (`tⱼ` at `t3 + k`, `bⱼ`, `mⱼ` loaded into `yb`, `ym`), `T'ⱼ₋₁` in `s2`. -/
def row1 (tk k : Nat) (yb ym : Reg) : List Instr :=
  [.load .d .s2 .t3 tk, .load .d yb .t4 k, .load .d ym .a0 k] ++ mac .s2 .t6 yb .s0 ++ mac .s2 .t2 ym .s1

/-- Row `i + 1`'s step at `j - 1` on `T'ⱼ₋₁` (`s2`), `bⱼ₋₁`, `mⱼ₋₁` in `xb`, `xm`, stored at
`t3 + off`. -/
def row2 (off : Nat) (xb xm : Reg) : List Instr :=
  mac .s2 .s5 xb .s7 ++ mac .s2 .s6 xm .s8 ++ [.store .d .s2 .t3 off]

/-- `t3` at word `j - 2` of `T`, `t4`, `a0` at word `j` of `b`, `m`. -/
def stepM (k : Nat) (xb xm yb ym : Reg) : List Instr := row1 (k + 16) k yb ym ++ row2 k xb xm

def grp2 : List Instr :=
  stepM 0 .a6 .a7 .s9 .s10 ++ stepM 8 .s9 .s10 .a6 .a7 ++ [.addi .t3 .t3 16, .addi .t4 .t4 16, .addi .a0 .a0 16]

/-- `a0 := m`, `a5 - 16 (w + 2)`. -/
def mBase (rd : Reg) : List Instr :=
  [.shift .sll .d .s2 .t0 3, .addi .s2 .s2 16, .shift .sll .d .s2 .s2 1, .sub rd .a5 .s2]

def head2 : List Instr :=
  mBase .a0 ++ [.addi .t3 .a5 0, .addi .t4 .a4 0,
    .load .d .t6 .a3 0, .load .d .s5 .a3 8, .addi .a3 .a3 16,
    .load .d .a6 .t4 0, .load .d .a7 .a0 0, .load .d .s4 .t3 0,
    -- row i, word 0: s₀ = t₀ + aᵢ b₀, u, d.
    .mul .s2 .t6 .a6, .mulhu .s3 .t6 .a6, .add .s2 .s2 .s4, .sltu .s4 .s2 .s4, .add .s0 .s3 .s4,
    .mul .t2 .s2 .t1, .mul .s3 .t2 .a7, .mulhu .s4 .t2 .a7, .add .s3 .s3 .s2, .sltu .s3 .s3 .s2,
    .add .s1 .s4 .s3] ++
  row1 8 8 .s9 .s10 ++
  -- row i + 1, word 0 on T'₀ (s2): u', its carries.
  [.mul .s3 .s5 .a6, .mulhu .s4 .s5 .a6, .add .s2 .s2 .s3, .sltu .s3 .s2 .s3, .add .s7 .s4 .s3,
    .mul .s6 .s2 .t1, .mul .s3 .s6 .a7, .mulhu .s4 .s6 .a7, .add .s3 .s3 .s2, .sltu .s3 .s3 .s2,
    .add .s8 .s4 .s3,
    .addi .a6 .s9 0, .addi .a7 .s10 0,
    .addi .t4 .t4 16, .addi .a0 .a0 16,
    .addi .t5 .t0 (-2), .shift .srl .d .t5 .t5 1]

def top2 : List Instr :=
  [.load .d .s4 .t3 16, .add .s0 .s0 .s4, .sltu .s4 .s0 .s4, .add .s0 .s0 .s1, .sltu .s3 .s0 .s1,
    .add .s11 .s4 .s3, .addi .s2 .s0 0] ++
  row2 0 .a6 .a7 ++
  [.add .s11 .s11 .s7, .sltu .s3 .s11 .s7, .add .s11 .s11 .s8, .sltu .s4 .s11 .s8, .add .s3 .s3 .s4,
    .store .d .s11 .t3 8, .store .d .s3 .t3 16, .addi .a1 .a1 (-1)]

def tail2 : Prog isa :=
  .seq zeroAcc (.seq (.block [.shift .srl .d .a1 .t0 1])
    (.seq (.loop (.seq (.block head2) (.seq (countLoop? grp2) (.block top2))) (.nonzero .a1))
      (.seq restoreSubMod64 selectAcc64)))

/-! ## Squaring with a two-row reduction

At each word `p`, rows `i` (`u` in `s0`, carry `s1`) and `i + 1` (`u` in `s6`, carry `s7`)
both added in one load and store; `m`'s words alternate between `s10`, `s11`, `m` at `s9`. -/

def redStep (k : Nat) (x y : Reg) : List Instr :=
  [.load .d .s2 .t4 k, .load .d y .a0 k] ++
  [.mul .s3 .s0 y, .mulhu .s4 .s0 y, .add .s2 .s2 .s3, .sltu .s3 .s2 .s3, .add .s4 .s4 .s3,
    .add .s2 .s2 .s1, .sltu .s1 .s2 .s1, .add .s1 .s4 .s1] ++
  mac .s2 .s6 x .s7 ++ [.store .d .s2 .t4 k]

def redGrp : List Instr :=
  redStep 0 .s10 .s11 ++ redStep 8 .s11 .s10 ++ [.addi .t4 .t4 16, .addi .a0 .a0 16]

def redHead : List Instr :=
  [.load .d .s4 .t3 0, .mul .s0 .s4 .t1, .load .d .s11 .s9 0, .load .d .s10 .s9 8,
    .mul .s2 .s0 .s11, .mulhu .s3 .s0 .s11, .add .s2 .s2 .s4, .sltu .s2 .s2 .s4, .add .s1 .s3 .s2,
    .load .d .s2 .t3 8,
    .mul .s3 .s0 .s10, .mulhu .s4 .s0 .s10, .add .s2 .s2 .s3, .sltu .s3 .s2 .s3, .add .s4 .s4 .s3,
    .add .s2 .s2 .s1, .sltu .s1 .s2 .s1, .add .s1 .s4 .s1,
    .mul .s6 .s2 .t1,
    .mul .s3 .s6 .s11, .mulhu .s4 .s6 .s11, .add .s3 .s3 .s2, .sltu .s3 .s3 .s2, .add .s7 .s4 .s3,
    .addi .t4 .t3 16, .addi .a0 .s9 16, .addi .t5 .t0 (-2), .shift .srl .d .t5 .t5 1]

def redTop2 : List Instr :=
  [.load .d .s4 .t4 0, .add .s4 .s4 .s1, .sltu .s3 .s4 .s1, .add .s4 .s4 .a1, .sltu .s2 .s4 .a1,
    .add .s8 .s3 .s2,
    .mul .s2 .s6 .s10, .mulhu .s3 .s6 .s10, .add .s4 .s4 .s2, .sltu .s2 .s4 .s2, .add .s3 .s3 .s2,
    .add .s4 .s4 .s7, .sltu .s7 .s4 .s7, .add .s7 .s3 .s7, .store .d .s4 .t4 0,
    .load .d .s4 .t4 8, .add .s4 .s4 .s7, .sltu .s3 .s4 .s7, .add .s4 .s4 .s8, .sltu .s2 .s4 .s8,
    .add .a1 .s3 .s2, .store .d .s4 .t4 8,
    .addi .t3 .t3 16, .addi .t2 .t2 (-1)]

def reduce2 : Prog isa :=
  .seq (.block ([.addi .t3 .a5 0, .shift .srl .d .t2 .t0 1, .li .a1 0] ++ mBase .s9))
    (.loop (.seq (.block redHead) (.seq (countLoop? redGrp) (.block redTop2))) (.nonzero .t2))

def sqrTail2 : Prog isa :=
  .seq zeroT (.seq cross (.seq diag (.seq reduce2
    (.seq (.block (restoreA7 ++ finishPre)) (.seq subMod64 (.seq selectAcc64 (.block finishPost)))))))

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}(ws: *mut u64, w: usize, count: usize) " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto17

open Proto17 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto17.rs"
  let fns : List (String × Prog isa) := [
    ("vg_p17_mul_base", mulLoop tail),
    ("vg_p17_mul_two", mulLoop tail2),
    ("vg_p17_sqr_base", sqrLoop sqrTail),
    ("vg_p17_sqr_two", sqrLoop sqrTail2),
    ("vg_p17_sqr_bymul", sqrByMulLoop tail2)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    String.join (fns.map fun (n, c) => emitFn n c))
