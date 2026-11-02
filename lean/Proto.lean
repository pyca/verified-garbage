import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul
import VerifiedGarbage.TCB.RISCV64.Target

/-! Throwaway, unproven: prints prototype Montgomery code for timing on RISE. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

namespace Proto

def save : List Instr :=
  (List.range 12).flatMap fun i =>
    [.store .d ([Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11].getD i .s0) .a0 (128 + 8 * i)]
def restore : List Instr :=
  ((List.range 12).filter (· != 6)).flatMap (fun i =>
    [.load .d ([Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11].getD i .s0) .s6 (128 + 8 * i)]) ++
  [.load .d .s6 .s6 (128 + 8 * 6)]

/-- proto(ws = a0, w = a1, count = a2): arrays of w+2 words from ws+256; `count` operations. -/
def setup : List Instr :=
  [.addi .s6 .a0 0, .addi .s7 .a2 0, .addi .t0 .a1 0, .shift .sll .d .s5 .a1 3, .addi .s5 .s5 16,
   .addi .a7 .a0 256, .load .d .t1 .a0 56]
def base (rd : Reg) (j : Nat) : List Instr := .addi rd .a7 0 :: List.replicate j (.add rd rd .s5)

def mulLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a4 6 ++ base .a5 2 ++ base .a6 3)) (.seq op
      (.block [.addi .s7 .s7 (-1)]))) (.nonzero .s7)) (.block restore))

/-! ## A dedicated squaring: `[o] = a² R⁻¹ mod m`, with `T` (2w+2 words) at a5 (arrays 2..3), tmp at a6 (array 7 here). -/

/-- T := 0 (2w+2 words). -/
def zeroT : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .add .t5 .t0 .t0, .addi .t5 .t5 2, .li .s0 0])
    (countLoop .t5 [.store .d .s0 .t3 0, .addi .t3 .t3 8])

/-- mac at pointers: s3:hi s2... T[t4] += s0 * [a0] + s1 (carry in s1). -/
def mac (k : Nat) : List Instr :=
  [.load .d .s2 .a0 k, .load .d .s4 .t4 k, .mul .s3 .s0 .s2, .mulhu .s2 .s0 .s2,
   .add .s3 .s3 .s4, .sltu .s4 .s3 .s4, .add .s2 .s2 .s4,
   .add .s3 .s3 .s1, .sltu .s4 .s3 .s1, .add .s1 .s2 .s4, .store .d .s3 .t4 k]

def macLoop : Prog isa :=
  .ite (.zero .t5) (.block []) (countLoop .t5 (mac 0 ++ [.addi .a0 .a0 8, .addi .t4 .t4 8]))

/-- Unrolled by 4 with a remainder loop: t5 = count. -/
def macRun : Prog isa :=
  .seq (.block [.logicImm .and .t2 .t5 3, .shift .srl .d .t5 .t5 2])
    (.seq (.ite (.zero .t5) (.block []) (countLoop .t5 (mac 0 ++ mac 8 ++ mac 16 ++ mac 24 ++
      [.addi .a0 .a0 32, .addi .t4 .t4 32])))
      (.ite (.zero .t2) (.block []) (countLoop .t2 (mac 0 ++ [.addi .a0 .a0 8, .addi .t4 .t4 8]))))

/-- Cross products: for i in 0..w-2: T[i+1..i+w-1] += a_i * a[i+1..w-1], carry to T[i+w]. -/
def cross : Prog isa :=
  .seq (.block [.addi .t6 .a3 0, .addi .a1 .t0 (-1), .addi .t1 .a5 8])
    (.loop (.seq (.block [.load .d .s0 .t6 0, .li .s1 0, .addi .a0 .t6 8, .addi .t4 .t1 0, .addi .t5 .a1 0])
      (.seq macRun (.block [.store .d .s1 .t4 0, .addi .t6 .t6 8, .addi .t1 .t1 16, .addi .a1 .a1 (-1)])))
      (.nonzero .a1))

/-- T := 2 T + diag(a_i²). sh in t1, carry in s1. -/
def diag : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t6 .a3 0, .addi .t5 .t0 0, .li .t1 0, .li .s1 0])
    (countLoop .t5 [.load .d .s0 .t3 0, .load .d .s2 .t3 8, .shift .srl .d .s3 .s0 63, .shift .sll .d .s0 .s0 1,
      .logic .or .s0 .s0 .t1, .shift .srl .d .t1 .s2 63, .shift .sll .d .s2 .s2 1, .logic .or .s2 .s2 .s3,
      .load .d .s3 .t6 0, .mul .s4 .s3 .s3, .mulhu .s3 .s3 .s3,
      .add .s0 .s0 .s1, .sltu .s1 .s0 .s1, .add .s0 .s0 .s4, .sltu .s4 .s0 .s4, .add .s1 .s1 .s4,
      .add .s2 .s2 .s3, .sltu .s3 .s2 .s3, .add .s2 .s2 .s1, .sltu .s1 .s2 .s1, .add .s1 .s1 .s3,
      .store .d .s0 .t3 0, .store .d .s2 .t3 8, .addi .t3 .t3 16, .addi .t6 .t6 8])

/-- Montgomery reduction of T (2w words) by rows; minv at header word 7 (ws+56) kept in t1 reloaded. top carry in t2' := a1. -/
def reduce : Prog isa :=
  .seq (.block [.addi .t6 .a5 0, .addi .t5 .t0 0, .li .a1 0, .addi .t3 .t5 0])
    (.loop (.seq (.block [.load .d .s0 .t6 0, .load .d .t1 .s6 56, .mul .s0 .s0 .t1, .li .s1 0, .addi .a0 .a7 0,
        .addi .t4 .t6 0, .addi .t5 .t0 0])
      (.seq macRun (.block [.load .d .s2 .t4 0, .add .s2 .s2 .s1, .sltu .s1 .s2 .s1, .add .s2 .s2 .a1,
        .sltu .a1 .s2 .a1, .add .a1 .a1 .s1, .store .d .s2 .t4 0, .addi .t6 .t6 8, .addi .t3 .t3 (-1)])))
      (.nonzero .t3))

/-- After reduce: result at T + 8w (w words) with top word a1 stored at T[2w]. -/
def sqrTail : Prog isa :=
  .seq zeroT (.seq cross (.seq diag (.seq reduce
    (.seq (.block [.shift .sll .d .t3 .t0 3, .add .t3 .t3 .t6, .store .d .a1 .t3 0,
      .addi .a5 .t6 0])
      (.seq subMod64 selectAcc64)))))

def sqrLoop : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a5 2 ++ base .a6 7)) (.seq sqrTail
      (.block [.addi .s7 .s7 (-1)]))) (.nonzero .s7)) (.block restore))

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}(ws: *mut u64, w: usize, count: usize) " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto

def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto.rs"
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    Proto.emitFn "vg_proto_mont_mul" (Proto.mulLoop tail) ++ Proto.emitFn "vg_proto_mont_sqr" Proto.sqrLoop)
