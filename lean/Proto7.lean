import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr

/-! Throwaway, unproven: variants of the RISC-V Montgomery multiplication and squaring, and
multiplier micro-benchmarks, printed for timing on RISE. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

namespace Proto7

/-! ## Harness (as `Proto.lean`'s) -/

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

/-- `count` multiplications `[5] = [5] [6] R⁻¹` (T at array 2, tmp at 3). -/
def mulLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a4 6 ++ base .a5 2 ++ base .a6 4)) (.seq op
      (.block [.addi .s7 .s7 (-1)]))) (.nonzero .s7)) (.block restore))

/-- `count` squarings `[5] = [5]² R⁻¹` (T at arrays 2–3, tmp at 4). -/
def sqrLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a5 2 ++ base .a6 4)) (.seq op
      (.block [.addi .s7 .s7 (-1)]))) (.nonzero .s7)) (.block restore))

/-! ## Variant F: each product as `mulhu hi` then `mul lo` with `hi` distinct from the sources
(the pair RISC-V's spec suggests for macro-op fusion); otherwise the same instructions. -/

def fiosHeadF : List Instr :=
  [.load .d .t6 .a3 0, .addi .a3 .a3 8, .load .d .s3 .a4 0, .load .d .s2 .a5 0,
    .mulhu .s0 .t6 .s3, .mul .s3 .t6 .s3, .add .s2 .s2 .s3, .sltu .s4 .s2 .s3, .add .s0 .s0 .s4,
    .mul .t2 .s2 .t1,
    .load .d .s3 .a7 0, .mulhu .s1 .t2 .s3, .mul .s3 .t2 .s3, .add .s3 .s3 .s2, .sltu .s4 .s3 .s2,
    .add .s1 .s1 .s4,
    .addi .t3 .a5 0, .addi .t4 .a4 0, .addi .a0 .a7 0]

def fiosStepF (k : Nat) : List Instr :=
  [.load .d .s2 .t3 (k + 8), .add .s0 .s0 .s2, .sltu .s4 .s0 .s2,
    .load .d .s3 .t4 (k + 8), .mulhu .s2 .t6 .s3, .mul .s3 .t6 .s3,
    .add .s2 .s2 .s4, .add .s3 .s3 .s0, .sltu .s4 .s3 .s0, .add .s0 .s2 .s4,
    .add .s1 .s1 .s3, .sltu .s4 .s1 .s3,
    .load .d .s3 .a0 (k + 8), .mulhu .s2 .t2 .s3, .mul .s3 .t2 .s3,
    .add .s2 .s2 .s4, .add .s3 .s3 .s1, .sltu .s4 .s3 .s1, .add .s1 .s2 .s4, .store .d .s3 .t3 k]

def grp (step : Nat → List Instr) (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => step (8 * k)) ++
    [.addi .t3 .t3 ((8 * U : Nat) : Int), .addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

/-- A round with its head, step and unroll `U` (a power of two). -/
def roundV (head : List Instr) (step : Nat → List Instr) (U : Nat) : Prog isa :=
  .seq (.block (head ++ [.addi .t5 .t0 (-1), .logicImm .and .t5 .t5 ((U - 1 : Nat) : Int)]))
    (.seq (countLoop? (grp step 1)) (.seq (.block [.addi .t5 .t0 (-1), .shift .srl .d .t5 .t5 (Nat.log2 U)])
      (.seq (countLoop? (grp step U)) (.block fiosTop))))

def tailV (head : List Instr) (step : Nat → List Instr) (U : Nat) : Prog isa :=
  .seq zeroAcc (.seq (.loop (.seq (roundV head step U) (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1))
    (.seq subMod64 selectAcc64))

/-! Squaring variants. -/

def sqrMacF (k : Nat) : List Instr :=
  [.load .d .s4 .t4 k, .add .s1 .s1 .s4, .sltu .s4 .s1 .s4,
    .load .d .s2 .a0 k, .mulhu .s3 .s0 .s2, .mul .s2 .s0 .s2, .add .s3 .s3 .s4,
    .add .s2 .s2 .s1, .sltu .s4 .s2 .s1, .add .s1 .s3 .s4, .store .d .s2 .t4 k]

def macGrp (mac : Nat → List Instr) (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => mac (8 * k)) ++
    [.addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

def macRunV (mac : Nat → List Instr) (U : Nat) : Prog isa :=
  .seq (.block [.logicImm .and .t6 .t5 ((U - 1 : Nat) : Int), .shift .srl .d .t5 .t5 (Nat.log2 U)])
    (.seq (countLoopR? .t5 (macGrp mac U)) (countLoopR? .t6 (macGrp mac 1)))

def crossV (mr : Prog isa) : Prog isa :=
  .seq (.block [.addi .t3 .a3 0, .addi .a1 .t0 (-1), .addi .t2 .a5 8])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .li .s1 0, .addi .a0 .t3 8, .addi .t4 .t2 0,
        .addi .t5 .a1 0])
      (.seq mr (.block [.store .d .s1 .t4 0, .addi .t3 .t3 8, .addi .t2 .t2 16,
        .addi .a1 .a1 (-1)])))
      (.nonzero .a1))

def diagStepF : List Instr :=
  [.load .d .s2 .t3 0, .load .d .s3 .t3 8, .shift .srl .d .s4 .s2 63, .shift .sll .d .s2 .s2 1,
    .add .s2 .s2 .t2, .shift .srl .d .t2 .s3 63, .shift .sll .d .s3 .s3 1, .add .s3 .s3 .s4,
    .load .d .s4 .a0 0, .add .s1 .s1 .s2, .sltu .s2 .s1 .s2, .mulhu .s0 .s4 .s4, .mul .s4 .s4 .s4,
    .add .s0 .s0 .s2, .add .s4 .s4 .s1, .sltu .s2 .s4 .s1, .add .s0 .s0 .s2, .add .s3 .s3 .s0,
    .sltu .s1 .s3 .s0, .store .d .s4 .t3 0, .store .d .s3 .t3 8, .addi .t3 .t3 16, .addi .a0 .a0 8]

def diagV (st : List Instr) : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .a0 .a3 0, .addi .t5 .t0 0, .li .t2 0, .li .s1 0])
    (countLoop .t5 st)

def reduceV (mr : Prog isa) : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t2 .t0 0, .li .a1 0])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .mul .s0 .s0 .t1, .li .s1 0, .addi .a0 .a7 0,
        .addi .t4 .t3 0, .addi .t5 .t0 0])
      (.seq mr (.block redTop)))
      (.nonzero .t2))

def sqrV (mac : Nat → List Instr) (U : Nat) (dst : List Instr) : Prog isa :=
  .seq zeroT (.seq (crossV (macRunV mac U)) (.seq (diagV dst) (.seq (reduceV (macRunV mac U))
    (.seq (.block finishPre) (.seq subMod64 (.seq selectAcc64 (.block finishPost)))))))


/-! ## Variant C: three operations on each carry chain per word: `t` (and `x`) added into the
product's low word first, the carry `c` (and `d`) last. -/

def fiosHeadC : List Instr :=
  [.load .d .t6 .a3 0, .addi .a3 .a3 8, .load .d .s3 .a4 0, .load .d .s2 .a5 0,
    .mul .s4 .t6 .s3, .mulhu .s0 .t6 .s3, .add .s2 .s2 .s4, .sltu .s4 .s2 .s4, .add .s0 .s0 .s4,
    .mul .t2 .s2 .t1,
    .load .d .s3 .a7 0, .mul .s4 .t2 .s3, .mulhu .s1 .t2 .s3, .add .s4 .s4 .s2, .sltu .s4 .s4 .s2,
    .add .s1 .s1 .s4,
    .addi .t3 .a5 0, .addi .t4 .a4 0, .addi .a0 .a7 0]

def fiosStepC (k : Nat) : List Instr :=
  [.load .d .s2 .t3 (k + 8), .load .d .s3 .t4 (k + 8),
    .mul .s4 .t6 .s3, .mulhu .s3 .t6 .s3,
    .add .s4 .s4 .s2, .sltu .s2 .s4 .s2, .add .s3 .s3 .s2,
    .add .s4 .s4 .s0, .sltu .s2 .s4 .s0, .add .s0 .s3 .s2,
    .load .d .s3 .a0 (k + 8), .mul .s2 .t2 .s3, .mulhu .s3 .t2 .s3,
    .add .s2 .s2 .s4, .sltu .s4 .s2 .s4, .add .s3 .s3 .s4,
    .add .s2 .s2 .s1, .sltu .s4 .s2 .s1, .add .s1 .s3 .s4, .store .d .s2 .t3 k]

def sqrMacC (k : Nat) : List Instr :=
  [.load .d .s4 .t4 k, .load .d .s2 .a0 k, .mul .s3 .s0 .s2, .mulhu .s2 .s0 .s2,
    .add .s3 .s3 .s4, .sltu .s4 .s3 .s4, .add .s2 .s2 .s4,
    .add .s3 .s3 .s1, .sltu .s4 .s3 .s1, .add .s1 .s2 .s4, .store .d .s3 .t4 k]

/-! ## Micro-benchmarks: `count` iterations of 16 operations, the sources `a0` and `a1`. -/

def dsts : List Reg := [.t2, .t3, .t4, .t5, .t6, .a3, .a4, .a5, .a6, .a7, .t0, .t1]

def microLoop (ops : List Instr) : Prog isa :=
  .seq (.block [.addi .a2 .a2 0])
    (.loop (.block (ops ++ [.addi .a2 .a2 (-1)])) (.nonzero .a2))

/-- 16 independent `mul`s. -/
def kMul : List Instr := (List.range 16).map fun i => .mul (dsts.getD (i % 12) .t2) .a0 .a1
/-- 8 pairs `mulhu hi; mul lo` (fusable). -/
def kFused : List Instr := (List.range 8).flatMap fun i =>
  [.mulhu (dsts.getD (2 * i % 12) .t2) .a0 .a1, .mul (dsts.getD ((2 * i + 1) % 12) .t2) .a0 .a1]
/-- 8 pairs `mul lo; mulhu hi`. -/
def kPair : List Instr := (List.range 8).flatMap fun i =>
  [.mul (dsts.getD (2 * i % 12) .t2) .a0 .a1, .mulhu (dsts.getD ((2 * i + 1) % 12) .t2) .a0 .a1]
/-- 16 independent `mulhu`s. -/
def kMulhu : List Instr := (List.range 16).map fun i => .mulhu (dsts.getD (i % 12) .t2) .a0 .a1
/-- 16 independent `add`s. -/
def kAdd : List Instr := (List.range 16).map fun i => .add (dsts.getD (i % 12) .t2) .a0 .a1

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}(ws: *mut u64, w: usize, count: usize) " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto7

open Proto7 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto7.rs"
  let fns : List (String × Prog isa) := [
    ("vg_p7_mul_base", mulLoop tail),
    ("vg_p7_mul_f", mulLoop (tailV fiosHeadF fiosStepF 4)),
    ("vg_p7_mul_u8", mulLoop (tailV fiosHead fiosStep 8)),
    ("vg_p7_mul_fu8", mulLoop (tailV fiosHeadF fiosStepF 8)),
    ("vg_p7_sqr_base", sqrLoop sqrTail),
    ("vg_p7_sqr_f", sqrLoop (sqrV sqrMacF 4 diagStepF)),
    ("vg_p7_sqr_u8", sqrLoop (sqrV sqrMac 8 diagStep)),
    ("vg_p7_sqr_fu8", sqrLoop (sqrV sqrMacF 8 diagStepF)),
    ("vg_p7_mul_c", mulLoop (tailV fiosHeadC fiosStepC 4)),
    ("vg_p7_mul_cu8", mulLoop (tailV fiosHeadC fiosStepC 8)),
    ("vg_p7_sqr_c", sqrLoop (sqrV sqrMacC 4 diagStep)),
    ("vg_p7_sqr_cu8", sqrLoop (sqrV sqrMacC 8 diagStep)),
    ("vg_p7_k_mul", microLoop kMul),
    ("vg_p7_k_fused", microLoop kFused),
    ("vg_p7_k_pair", microLoop kPair),
    ("vg_p7_k_mulhu", microLoop kMulhu),
    ("vg_p7_k_add", microLoop kAdd)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    String.join (fns.map fun (n, c) => emitFn n c))
