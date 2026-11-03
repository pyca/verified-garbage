import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues

/-! Throwaway, unproven: `vg_rsa_crt_values` whose divisions' passes run four words at a
time (the rest one at a time first). Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div
open VG.Impl.Rsa.RISCV64.CrtValues

namespace Proto20

/-- `passBody` at offset `o`, without the pointer advance. -/
def passAt (o : Nat) : List Instr :=
  [.load .d .t5 .t0 o, .shift .sll .d .t6 .t5 1, .logic .or .t6 .t6 .t3, .shift .srl .d .t3 .t5 63,
    .load .d .t5 .t1 o, .logic .xor .t5 .t5 .a4, .add .t6 .t6 .t4, .sltu .a5 .t6 .t4,
    .add .t6 .t6 .t5, .sltu .t4 .t6 .t5, .logic .or .t4 .t4 .a5, .store .d .t6 .t0 o]

def pass4 : List Instr := passAt 0 ++ passAt 8 ++ passAt 16 ++ passAt 24 ++ [.addi .t0 .t0 32, .addi .t1 .t1 32]

/-- The pass over `k + 1` words: `(k + 1) mod 4` one at a time, then four at a time. -/
def passes (k : Reg) : Prog isa :=
  .seq (.block [.addi .t2 k 1, .logicImm .and .t2 .t2 3])
    (.seq (.ite (.zero .t2) (.block []) (countLoop .t2 passBody))
      (.seq (.block [.addi .t2 k 1, .shift .srl .d .t2 .t2 2])
        (.ite (.zero .t2) (.block []) (countLoop .t2 pass4))))

def stepK' (q r d : Nat) (k : Reg) : Prog isa :=
  .seq (.block (qword q ++ [.load .d .t5 .t2 0, .shift .srl .d .t3 .t5 63] ++ ptr .t0 r ++ ptr .t1 d ++
      [.logicImm .and .t4 .a4 1]))
    (.seq (passes k)
      (.block ([.shift .srl .d .t5 .t6 63, .addi .a4 .t5 (-1), .logicImm .and .a5 .a4 1] ++ qword q ++
        [.load .d .t5 .t2 0, .shift .sll .d .t5 .t5 1, .logic .or .t5 .t5 .a5, .store .d .t5 .t2 0,
          .addi .s7 .s7 (-1)])))

def divK' (q r d : Nat) (k : Reg) : Prog isa :=
  .seq (init r) (.seq (.loop (stepK' q r d k) (.nonzero .s7)) (fixK r d k))

def divL' (q r d : Nat) (len : Reg) : Prog isa := .seq (.block (wordsOf len)) (divK' q r d .s8)

def divChecks' : Prog isa := seqs [
  copy aDD aP, .block (bitOf sPodd aP), divL' aDQ aDR aDD .s4, eqS sE1 aDQ aQ, eqS sE2 aDR aZero]

def checks' : Prog isa := .seq (.block lenTest) (.ite (.zero .t5) mulChecks divChecks')

def dParts' : Prog isa := seqs [
  copy aDQ aD, copy aDD aP, .block (clrLow aDD), divL' aDQ aDR2 aDD .s4,
  copy aDQ aD, copy aDD aQ, .block (clrLow aDD), divL' aDQ aDR3 aDD .s6]

def code' : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) (seqs [setup, loads, seqs [checks', invPart, dParts'], stores]) fail) (.block restore)))

def sigCrt : String :=
  "(dp: *mut u8, dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize, n: *const u8, n_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, d: *const u8, d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto20

open Proto20 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto20.rs"
  let fns : List (String × String × Prog isa) := [
    ("vg_p20_crt_base", sigCrt, VG.Impl.Rsa.RISCV64.CrtValues.code),
    ("vg_p20_crt_u4", sigCrt, code')]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, s, c) => emitFn n s c))
