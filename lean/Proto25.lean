import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr

/-! Throwaway, unproven: one-level Karatsuba Montgomery squaring (even `w`). Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

namespace Proto25

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

/-! ## Karatsuba squaring, one level, even `w` (`h = w / 2`)

`s8 = h`, `s9` the stride, `s10` `a`'s base, `s11` `T`'s base; temporaries `Z0`, `Z2`, `S`, `Z1` in arrays
8–11 (of `T`'s working space, `a5 + (j - 2) s9`). -/

def arr (rd : Reg) (j : Nat) : List Instr :=
  .addi rd .s11 0 :: (if j ≥ 2 then List.replicate (j - 2) (.add rd rd .s9) else [])

/-- `[t3] += ([t4] & s0) + carry` over `t5` words, then the carry through `t6` more words of `[t3]`. -/
def addTo : Prog isa :=
  .seq (.block [.li .s1 0])
  (.seq (countLoopR? .t5 [.load .d .s2 .t3 0, .load .d .s3 .t4 0, .logic .and .s3 .s3 .s0, .add .s2 .s2 .s3,
      .sltu .s4 .s2 .s3, .add .s2 .s2 .s1, .sltu .s3 .s2 .s1, .logic .or .s1 .s4 .s3, .store .d .s2 .t3 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8])
    (countLoopR? .t6 [.load .d .s2 .t3 0, .add .s2 .s2 .s1, .sltu .s1 .s2 .s1, .store .d .s2 .t3 0,
      .addi .t3 .t3 8]))

/-- `[t3] -= [t4]` over `t5` words (the borrow out dropped). -/
def subFrom : Prog isa :=
  .seq (.block [.li .s1 0])
    (countLoopR? .t5 [.load .d .s2 .t3 0, .load .d .s3 .t4 0, .sltu .s4 .s2 .s3, .sub .s2 .s2 .s3,
      .sltu .s3 .s2 .s1, .sub .s2 .s2 .s1, .logic .or .s1 .s4 .s3, .store .d .s2 .t3 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8])

/-- `t5` words from `t4` to `t3`. -/
def copyW : Prog isa :=
  countLoopR? .t5 [.load .d .s2 .t4 0, .store .d .s2 .t3 0, .addi .t3 .t3 8, .addi .t4 .t4 8]

/-- The product `[a3]²` (`t0` words) into the `2 t0 + 2` words at `a5`. -/
def sqrProd : Prog isa := .seq zeroT (.seq cross diag)

def seqL : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (seqL ps)

/-- `t3 :=` `Z1`'s word `h`, `t4 :=` `S`, `s5 :=` `S[h]` (the carry `c`), `s0 := -c`; `t5 = h`, `t6 = 2`. -/
def corrSetup : List Instr :=
  arr .t4 10 ++ [.shift .sll .d .t2 .s8 3, .add .t2 .t2 .t4, .load .d .s5 .t2 0, .li .s0 0,
      .sub .s0 .s0 .s5] ++ arr .t3 11 ++ [.shift .sll .d .t2 .s8 3, .add .t3 .t3 .t2, .addi .t5 .s8 0, .li .t6 2]

def karaSqr : Prog isa := seqL [
  .block [.shift .srl .d .s8 .t0 1, .shift .sll .d .s9 .t0 3, .addi .s9 .s9 16, .addi .s10 .a3 0,
      .addi .s11 .a5 0],
  .block (arr .t3 10 ++ [.addi .t4 .s10 0, .shift .sll .d .t6 .s8 3, .add .t6 .t6 .s10, .addi .t5 .s8 0,
      .li .s1 0]),
  countLoop .t5 [.load .d .s2 .t4 0, .load .d .s3 .t6 0, .add .s2 .s2 .s3, .sltu .s4 .s2 .s3,
      .add .s2 .s2 .s1, .sltu .s3 .s2 .s1, .logic .or .s1 .s4 .s3, .store .d .s2 .t3 0, .addi .t3 .t3 8,
      .addi .t4 .t4 8, .addi .t6 .t6 8],
  .block [.store .d .s1 .t3 0, .li .s0 0, .store .d .s0 .t3 8],
  .block ([.addi .t0 .s8 0, .addi .a3 .s10 0] ++ arr .a5 8), sqrProd,
  .block ([.shift .sll .d .a3 .s8 3, .add .a3 .a3 .s10] ++ arr .a5 9), sqrProd,
  .block (arr .a3 10 ++ arr .a5 11), sqrProd,
  .block corrSetup, addTo,
  .block corrSetup, addTo,
  .block (arr .t3 11 ++ [.shift .sll .d .t2 .s8 4, .add .t3 .t3 .t2, .load .d .s2 .t3 0, .add .s2 .s2 .s5,
      .sltu .s1 .s2 .s5, .store .d .s2 .t3 0, .load .d .s2 .t3 8, .add .s2 .s2 .s1, .store .d .s2 .t3 8]),
  .block (arr .t3 11 ++ arr .t4 8 ++ [.shift .sll .d .t5 .s8 1, .addi .t5 .t5 2]), subFrom,
  .block (arr .t3 11 ++ arr .t4 9 ++ [.shift .sll .d .t5 .s8 1, .addi .t5 .t5 2]), subFrom,
  .block ([.addi .t3 .s11 0] ++ arr .t4 8 ++ [.shift .sll .d .t5 .s8 1]), copyW,
  .block (arr .t4 9 ++ [.shift .sll .d .t5 .s8 1]), copyW,
  .block [.li .s2 0, .store .d .s2 .t3 0, .store .d .s2 .t3 8],
  .block ([.shift .sll .d .t3 .s8 3, .add .t3 .t3 .s11] ++ arr .t4 11 ++
      [.shift .sll .d .t5 .s8 1, .addi .t5 .t5 2, .addi .t6 .s8 0, .li .s0 (-1)]), addTo,
  .block [.shift .sll .d .t0 .s8 1, .addi .a3 .s10 0, .addi .a5 .s11 0],
  reduce,
  .block (restoreA7 ++ finishPre), subMod64, selectAcc64, .block finishPost]

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}(ws: *mut u64, w: usize, count: usize) " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto25

open Proto25 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto25.rs"
  let fns : List (String × Prog isa) := [
    ("vg_p25_sqr_base", sqrLoop sqrTail),
    ("vg_p25_sqr_kara", sqrLoop karaSqr),
    ("vg_p25_mul_base", mulLoop tail)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    String.join (fns.map fun (n, c) => emitFn n c))
