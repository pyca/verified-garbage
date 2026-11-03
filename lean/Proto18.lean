import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-! Throwaway, unproven: a microbenchmark of the RISC-V multiplier's throughput and
latency. Each function runs `a0` iterations of a 64-instruction body (plus the loop's
`addi`/`bnez`), on registers only, caller-saved ones (`t0`–`t6`, `a1`–`a7`). Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

namespace Proto18

/-- Operands: large odd constants in `a1`–`a4`, and `t0`–`t6`, `a5`–`a7` seeded. -/
def seed : List Instr :=
  [.li .a1 0x567, .li .a2 0x321, .li .a3 0x6ce, .li .a4 0x5df,
   .shift .sll .d .a1 .a1 52, .addi .a1 .a1 0x1d, .shift .sll .d .a2 .a2 52, .addi .a2 .a2 0x3b,
   .shift .sll .d .a3 .a3 52, .addi .a3 .a3 0x55, .shift .sll .d .a4 .a4 52, .addi .a4 .a4 0x77,
   .addi .t0 .a1 0, .addi .t1 .a2 0, .addi .t2 .a3 0, .addi .t3 .a4 0,
   .addi .t4 .a1 1, .addi .t5 .a2 1, .addi .t6 .a3 1, .addi .a5 .a4 1,
   .addi .a6 .a1 2, .addi .a7 .a2 2]

/-- The accumulators. -/
def accs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a5]

def acc (k : Nat) : Reg := accs.getD (k % 8) .t0

/-- `64` instructions from `f k`. -/
def body (f : Nat → Instr) : List Instr := (List.range 64).map f

def loopOf (f : Nat → Instr) : Prog isa :=
  .seq (.block seed) (countLoop .a0 (body f))

def variants : List (String × (Nat → Instr)) := [
  -- ALU control: 8 independent chains of add.
  ("add8", fun k => .add (acc k) (acc k) .a1),
  -- Fully independent (fixed sources), 8 destinations.
  ("mul_ind", fun k => .mul (acc k) .a1 .a2),
  ("mulhu_ind", fun k => .mulhu (acc k) .a1 .a2),
  -- Alternating mul / mulhu, different operands.
  ("alt_ind", fun k => if k % 2 = 0 then .mul (acc k) .a1 .a2 else .mulhu (acc k) .a3 .a4),
  -- mul + mulhu on the same pair, as FIOS does.
  ("pair_ind", fun k => if k % 2 = 0 then .mul (acc k) .a1 .a2 else .mulhu (acc k) .a1 .a2),
  -- 4 and 8 accumulator chains.
  ("mul_acc4", fun k => .mul (acc (k % 4)) (acc (k % 4)) .a1),
  ("mul_acc8", fun k => .mul (acc k) (acc k) .a1),
  ("mulhu_acc4", fun k => .mulhu (acc (k % 4)) (acc (k % 4)) .a1),
  ("mulhu_acc8", fun k => .mulhu (acc k) (acc k) .a1),
  -- Dependent chains: latency.
  ("mul_dep", fun _ => .mul .t0 .t0 .a1),
  ("mulhu_dep", fun _ => .mulhu .t0 .t0 .a1),
  -- FIOS-like mix: one mul/mulhu pair per 3 adds (independent).
  ("mix_1to3", fun k => match k % 5 with
    | 0 => .mul (acc k) .a1 .a2 | 1 => .mulhu (acc k) .a1 .a2
    | _ => .add (acc (k + 3)) (acc (k + 3)) .a3)]

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}(n: usize) " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto18

open Proto18 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto18.rs"
  IO.FS.writeFile out ("//! Unproven microbenchmark, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    String.join (variants.map fun (n, f) => emitFn s!"vg_p18_{n}" (loopOf f)))
