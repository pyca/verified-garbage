import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Scrypt.RISCV64.RoMix

/-! Throwaway, unproven: `vg_scrypt_romix` with its copy into `V[i]` and its
`X xor V[j]` four doublewords a step. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Scrypt.RISCV64

namespace Proto22

/-- `[t1] ← [t0]`, `t2` steps of 32 bytes. -/
def copy4 : Prog isa :=
  .loop (.block [.load .d .t3 .t0 0, .load .d .t4 .t0 8, .load .d .t5 .t0 16, .load .d .t6 .t0 24,
    .store .d .t3 .t1 0, .store .d .t4 .t1 8, .store .d .t5 .t1 16, .store .d .t6 .t1 24,
    .addi .t0 .t0 32, .addi .t1 .t1 32, .addi .t2 .t2 (-1)]) (.nonzero .t2)

/-- `[t2] ← [t0] xor [t1]`, `t3` steps of 32 bytes. -/
def xor4 : Prog isa :=
  .loop (.block [.load .d .t4 .t0 0, .load .d .t5 .t1 0, .load .d .t6 .t0 8, .load .d .a6 .t1 8,
    .load .d .a7 .t0 16, .load .d .a0 .t1 16, .load .d .a1 .t0 24, .load .d .a2 .t1 24,
    .logic .xor .t4 .t4 .t5, .logic .xor .t6 .t6 .a6, .logic .xor .a7 .a7 .a0, .logic .xor .a1 .a1 .a2,
    .store .d .t4 .t2 0, .store .d .t6 .t2 8, .store .d .a7 .t2 16, .store .d .a1 .t2 24,
    .addi .t0 .t0 32, .addi .t1 .t1 32, .addi .t2 .t2 32, .addi .t3 .t3 (-1)]) (.nonzero .t3)

def step2' : Prog isa :=
  .seq (.block [mov .t0 .s4, mov .t1 .s8, .shift .srl .d .t2 .s6 5]) <|
  .seq copy4 <|
  .seq (blockMixTo true [mov .a0 .s8])
    (.block [.add .s8 .s8 .s6, .addi .s7 .s7 (-1)])

def step3' : Prog isa :=
  .seq (.block (jBlock true)) <|
  .seq (.block [.mul .t1 .t0 .s6, .add .t1 .t1 .s5, mov .t0 .s4, mov .t2 .s9, .shift .srl .d .t3 .s6 5]) <|
  .seq xor4 <|
  .seq (blockMixTo true [mov .a0 .s9])
    (.block [.addi .s7 .s7 (-1)])

def roMix' : Prog isa :=
  .seq (.block rmPrologue) <|
  .seq nLoop <|
  .seq (.block rmSetup) <|
  .seq (.loop step2' (.nonzero .s7)) <|
  .seq (.block rmMid) <|
  .seq (.loop step3' (.nonzero .s7))
    (.block rmEpilogue)

def sig : String := "(b: *mut u8, r: usize, v: *mut u8, vlen: usize, t: *mut u8, save: *mut u64)"

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun n => s!"scrypt::{n}") "crate" ++ "}\n"

end Proto22

open Proto22 in
def main (args : List String) : IO Unit := do
  let out := args.headD "scrypt_proto22.rs"
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    emitFn "vg_p22_romix_base" (roMix true) ++ emitFn "vg_p22_romix_u4" roMix')
