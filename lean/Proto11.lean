import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr

/-! Throwaway, unproven: RISC-V Montgomery multiplication and squaring that also write `a6`
and `a7` inside the rounds (the next word's `b` and `m`, or the operand's, loaded a step ahead
into them) and recompute them from `a5` and `t0` before the final subtraction, keeping
`tail`'s and `sqrTail`'s register interface. Printed for timing on RISE. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

namespace Proto11

/-! ## Harness (Proto8's; the multiplication's temporary at array 3, as `tail_ok` says;
after each call `a6 - a5` and `a5 - a7` stored at words 3 and 4 of array 7) -/

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

def sqrLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a5 2 ++ base .a6 4 ++ spill))
      (.seq op (.block (check ++ unspill)))) (.nonzero .s7)) (.block restore))

/-! ## Multiplication: `bⱼ` in `a6`, `mⱼ` in `a7`, the next word's loaded once they are used;
`a0` the pointer into `m` throughout, rewound at each round's end -/

/-- `fiosHead`, `m₀` through `a0`, and `b₁`, `m₁` into `a6`, `a7`. -/
def headP : List Instr :=
  [.load .d .t6 .a3 0, .addi .a3 .a3 8, .load .d .s3 .a4 0, .load .d .s2 .a5 0,
    .load .d .a6 .a4 8, .load .d .a7 .a0 8,
    .mul .s0 .t6 .s3, .mulhu .s3 .t6 .s3, .add .s2 .s2 .s0, .sltu .s4 .s2 .s0, .add .s0 .s3 .s4,
    .mul .t2 .s2 .t1,
    .load .d .s3 .a0 0, .mul .s1 .t2 .s3, .mulhu .s3 .t2 .s3, .add .s1 .s1 .s2, .sltu .s4 .s1 .s2,
    .add .s1 .s3 .s4,
    .addi .t3 .a5 0, .addi .t4 .a4 0]

/-- A step, three-operation carry chains (Proto7's C order). -/
def stepP (k : Nat) : List Instr :=
  [.load .d .s2 .t3 (k + 8), .mul .s4 .t6 .a6, .mulhu .s3 .t6 .a6, .load .d .a6 .t4 (k + 16),
    .add .s4 .s4 .s2, .sltu .s2 .s4 .s2, .add .s3 .s3 .s2,
    .add .s4 .s4 .s0, .sltu .s2 .s4 .s0, .add .s0 .s3 .s2,
    .mul .s2 .t2 .a7, .mulhu .s3 .t2 .a7, .load .d .a7 .a0 (k + 16),
    .add .s2 .s2 .s4, .sltu .s4 .s2 .s4, .add .s3 .s3 .s4,
    .add .s2 .s2 .s1, .sltu .s4 .s2 .s1, .add .s1 .s3 .s4, .store .d .s2 .t3 k]

/-- A step in `fiosStep`'s order. -/
def stepPO (k : Nat) : List Instr :=
  [.load .d .s2 .t3 (k + 8), .add .s0 .s0 .s2, .sltu .s4 .s0 .s2,
    .mul .s2 .t6 .a6, .mulhu .s3 .t6 .a6, .load .d .a6 .t4 (k + 16), .add .s3 .s3 .s4,
    .add .s2 .s2 .s0, .sltu .s4 .s2 .s0, .add .s0 .s3 .s4,
    .add .s1 .s1 .s2, .sltu .s4 .s1 .s2,
    .mul .s2 .t2 .a7, .mulhu .s3 .t2 .a7, .load .d .a7 .a0 (k + 16), .add .s3 .s3 .s4,
    .add .s2 .s2 .s1, .sltu .s4 .s2 .s1, .add .s1 .s3 .s4, .store .d .s2 .t3 k]

def grp (step : Nat → List Instr) (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => step (8 * k)) ++
    [.addi .t3 .t3 ((8 * U : Nat) : Int), .addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

/-- `a0` back from word `w - 1` of `m` to word 0, and the round counted. -/
def rewind : List Instr := [.shift .sll .d .s2 .t0 3, .sub .a0 .a0 .s2, .addi .a0 .a0 8, .addi .a1 .a1 (-1)]

/-- `a6 := a5 + 8 (w + 2)`, `a7 := a5 - 16 (w + 2)`: arrays 3 and 0 again. -/
def restoreA : List Instr :=
  [.shift .sll .d .s2 .t0 3, .addi .s2 .s2 16, .add .a6 .a5 .s2, .shift .sll .d .s3 .s2 1,
    .sub .a7 .a5 .s3]

def tailP (step : Nat → List Instr) : Prog isa :=
  .seq zeroAcc (.seq (.block [.addi .a0 .a7 0])
    (.seq (.loop (.seq (.seq (.block (headP ++ fiosRem)) (.seq (countLoop? (grp step 1))
        (.seq (.block fiosQuot) (.seq (countLoop? (grp step unroll)) (.block fiosTop)))))
      (.block rewind)) (.nonzero .a1))
    (.seq (.block restoreA) (.seq subMod64 selectAcc64))))

/-! ## Squaring: the row's operand word `yⱼ` in `a7`, the next one loaded once it is used -/

def macP (k : Nat) : List Instr :=
  [.load .d .s4 .t4 k, .mul .s3 .s0 .a7, .mulhu .s2 .s0 .a7, .load .d .a7 .a0 (k + 8),
    .add .s3 .s3 .s4, .sltu .s4 .s3 .s4, .add .s2 .s2 .s4,
    .add .s3 .s3 .s1, .sltu .s4 .s3 .s1, .add .s1 .s2 .s4, .store .d .s3 .t4 k]

def macGrpP (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => macP (8 * k)) ++
    [.addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

def macRunP : Prog isa :=
  .seq (.block [.logicImm .and .t6 .t5 7, .shift .srl .d .t5 .t5 3, .load .d .a7 .a0 0])
    (.seq (countLoopR? .t5 (macGrpP 8)) (countLoopR? .t6 (macGrpP 1)))

def crossP : Prog isa :=
  .seq (.block [.addi .t3 .a3 0, .addi .a1 .t0 (-1), .addi .t2 .a5 8])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .li .s1 0, .addi .a0 .t3 8, .addi .t4 .t2 0,
        .addi .t5 .a1 0])
      (.seq macRunP (.block [.store .d .s1 .t4 0, .addi .t3 .t3 8, .addi .t2 .t2 16,
        .addi .a1 .a1 (-1)])))
      (.nonzero .a1))

/-- `reduce`, `a0` at `m` from `a5 - 16 (w + 2)`, rewound by `w` words after each row. -/
def reduceP : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t2 .t0 0, .li .a1 0, .shift .sll .d .s2 .t0 3,
      .addi .s2 .s2 16, .shift .sll .d .s2 .s2 1, .sub .a0 .a5 .s2])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .mul .s0 .s0 .t1, .li .s1 0,
        .addi .t4 .t3 0, .addi .t5 .t0 0])
      (.seq macRunP (.block (redTop ++ [.shift .sll .d .s2 .t0 3, .sub .a0 .a0 .s2]))))
      (.nonzero .t2))

def restoreA7 : List Instr :=
  [.shift .sll .d .s2 .t0 3, .addi .s2 .s2 16, .shift .sll .d .s2 .s2 1, .sub .a7 .a5 .s2]

def sqrTailP : Prog isa :=
  .seq zeroT (.seq crossP (.seq diag (.seq reduceP
    (.seq (.block (restoreA7 ++ finishPre)) (.seq subMod64 (.seq selectAcc64 (.block finishPost)))))))

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}(ws: *mut u64, w: usize, count: usize) " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto11

open Proto11 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto11.rs"
  let fns : List (String × Prog isa) := [
    ("vg_p11_mul_base", mulLoop tail),
    ("vg_p11_mul_p", mulLoop (tailP stepP)),
    ("vg_p11_mul_po", mulLoop (tailP stepPO)),
    ("vg_p11_sqr_base", sqrLoop sqrTail),
    ("vg_p11_sqr_p", sqrLoop sqrTailP)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    String.join (fns.map fun (n, c) => emitFn n c))
