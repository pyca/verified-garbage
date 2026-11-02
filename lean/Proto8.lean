import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr

/-! Throwaway, unproven: RISC-V Montgomery multiplication and squaring variants that may also
write `s5`–`s10` (loads hoisted a step ahead, product scanning), printed for timing on RISE.
Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

namespace Proto8

/-! ## Harness (as `Proto7.lean`'s, but `s5`–`s7` spilled into array 7 around each call, since
the variants may write them) -/

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
/-- `s5`–`s7` into array 7 (`a7 + 7 s5`). -/
def spill : List Instr :=
  [.shift .sll .d .t2 .s5 3, .sub .t2 .t2 .s5, .add .t2 .t2 .a7,
   .store .d .s5 .t2 0, .store .d .s6 .t2 8, .store .d .s7 .t2 16]
/-- `s5`–`s7` back (the stride recomputed from `t0`), and the count down. -/
def unspill : List Instr :=
  [.shift .sll .d .t2 .t0 3, .addi .t2 .t2 16, .shift .sll .d .t3 .t2 3, .sub .t3 .t3 .t2,
   .add .t2 .t3 .a7, .load .d .s5 .t2 0, .load .d .s6 .t2 8, .load .d .s7 .t2 16,
   .addi .s7 .s7 (-1)]

def mulLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a4 6 ++ base .a5 2 ++ base .a6 4 ++ spill))
      (.seq op (.block unspill))) (.nonzero .s7)) (.block restore))

def sqrLoop (op : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.loop (.seq (.block (base .a2 5 ++ base .a3 5 ++ base .a5 2 ++ base .a6 4 ++ spill))
      (.seq op (.block unspill))) (.nonzero .s7)) (.block restore))

/-! ## FIOS variants -/

def grp (step : Nat → List Instr) (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => step (8 * k)) ++
    [.addi .t3 .t3 ((8 * U : Nat) : Int), .addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

/-- Proto7's three-operation carry chains (variant C). -/
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

/-- A step with its word's `t`, `b`, `m` already in `L`, the next word's loaded into `N`
(original order). -/
def stepH (L N : Reg × Reg × Reg) (k : Nat) : List Instr :=
  let (lt, lb, lm) := L; let (nt, nb, nm) := N
  [.load .d nt .t3 (k + 16), .load .d nb .t4 (k + 16), .load .d nm .a0 (k + 16),
    .add .s0 .s0 lt, .sltu .s4 .s0 lt, .mul .s2 .t6 lb, .mulhu .s3 .t6 lb, .add .s3 .s3 .s4,
    .add .s2 .s2 .s0, .sltu .s4 .s2 .s0, .add .s0 .s3 .s4,
    .add .s1 .s1 .s2, .sltu .s4 .s1 .s2, .mul .s2 .t2 lm, .mulhu .s3 .t2 lm, .add .s3 .s3 .s4,
    .add .s2 .s2 .s1, .sltu .s4 .s2 .s1, .add .s1 .s3 .s4, .store .d .s2 .t3 k]

/-- The same in variant C's order. -/
def stepHC (L N : Reg × Reg × Reg) (k : Nat) : List Instr :=
  let (lt, lb, lm) := L; let (nt, nb, nm) := N
  [.load .d nt .t3 (k + 16), .load .d nb .t4 (k + 16), .load .d nm .a0 (k + 16),
    .mul .s4 .t6 lb, .mulhu .s3 .t6 lb,
    .add .s4 .s4 lt, .sltu .s2 .s4 lt, .add .s3 .s3 .s2,
    .add .s4 .s4 .s0, .sltu .s2 .s4 .s0, .add .s0 .s3 .s2,
    .mul .s2 .t2 lm, .mulhu .s3 .t2 lm,
    .add .s2 .s2 .s4, .sltu .s4 .s2 .s4, .add .s3 .s3 .s4,
    .add .s2 .s2 .s1, .sltu .s4 .s2 .s1, .add .s1 .s3 .s4, .store .d .s2 .t3 k]

def LR : Reg × Reg × Reg := (.s5, .s6, .s7)
def NR : Reg × Reg × Reg := (.s8, .s9, .s10)

/-- Four hoisted steps (`L`, `N`, `L`, `N`: `L` holds the next word's after), the pointers
advanced. -/
def grpH (st : (Reg × Reg × Reg) → (Reg × Reg × Reg) → Nat → List Instr) : List Instr :=
  st LR NR 0 ++ st NR LR 8 ++ st LR NR 16 ++ st NR LR 24 ++
    [.addi .t3 .t3 32, .addi .t4 .t4 32, .addi .a0 .a0 32]

def preload : List Instr := [.load .d .s5 .t3 8, .load .d .s6 .t4 8, .load .d .s7 .a0 8]

def roundH (head : List Instr) (single : Nat → List Instr)
    (st : (Reg × Reg × Reg) → (Reg × Reg × Reg) → Nat → List Instr) : Prog isa :=
  .seq (.block (head ++ fiosRem)) (.seq (countLoop? (grp single 1))
    (.seq (.block (fiosQuot ++ preload)) (.seq (countLoop? (grpH st)) (.block fiosTop))))

def tailH (head : List Instr) (single : Nat → List Instr)
    (st : (Reg × Reg × Reg) → (Reg × Reg × Reg) → Nat → List Instr) : Prog isa :=
  .seq zeroAcc (.seq (.loop (.seq (roundH head single st) (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1))
    (.seq subMod64 selectAcc64))

/-- Proto7's variant C, unrolled by 4, not hoisted. -/
def tailC : Prog isa :=
  .seq zeroAcc (.seq (.loop (.seq (.seq (.block (fiosHeadC ++ fiosRem)) (.seq (countLoop? (grp fiosStepC 1))
    (.seq (.block fiosQuot) (.seq (countLoop? (grp fiosStepC 4)) (.block fiosTop)))))
    (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)) (.seq subMod64 selectAcc64))

/-! ## Squaring variants -/

def sqrMacC (k : Nat) : List Instr :=
  [.load .d .s4 .t4 k, .load .d .s2 .a0 k, .mul .s3 .s0 .s2, .mulhu .s2 .s0 .s2,
    .add .s3 .s3 .s4, .sltu .s4 .s3 .s4, .add .s2 .s2 .s4,
    .add .s3 .s3 .s1, .sltu .s4 .s3 .s1, .add .s1 .s2 .s4, .store .d .s3 .t4 k]

def macGrp (mac : Nat → List Instr) (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => mac (8 * k)) ++
    [.addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

/-- Proto7's best squaring row: C order, unrolled by 8. -/
def macRunV (mac : Nat → List Instr) (U : Nat) : Prog isa :=
  .seq (.block [.logicImm .and .t6 .t5 ((U - 1 : Nat) : Int), .shift .srl .d .t5 .t5 (Nat.log2 U)])
    (.seq (countLoopR? .t5 (macGrp mac U)) (countLoopR? .t6 (macGrp mac 1)))

/-- A hoisted step: this word's `t` and `y` in `L`, the next word's loaded into `N`. -/
def macH (L N : Reg × Reg) (k : Nat) : List Instr :=
  let (lt, la) := L; let (nt, na) := N
  [.load .d nt .t4 (k + 8), .load .d na .a0 (k + 8), .mul .s3 .s0 la, .mulhu .s2 .s0 la,
    .add .s3 .s3 lt, .sltu .s4 .s3 lt, .add .s2 .s2 .s4,
    .add .s3 .s3 .s1, .sltu .s4 .s3 .s1, .add .s1 .s2 .s4, .store .d .s3 .t4 k]

/-- A row: groups of four hoisted steps, then the rest one at a time (C order). -/
def macRunH : Prog isa :=
  .seq (.block [.logicImm .and .t6 .t5 3, .shift .srl .d .t5 .t5 2, .load .d .s5 .t4 0,
      .load .d .s6 .a0 0])
    (.seq (countLoopR? .t5 (macH (.s5, .s6) (.s7, .s8) 0 ++ macH (.s7, .s8) (.s5, .s6) 8 ++
        macH (.s5, .s6) (.s7, .s8) 16 ++ macH (.s7, .s8) (.s5, .s6) 24 ++
        [.addi .t4 .t4 32, .addi .a0 .a0 32]))
      (countLoopR? .t6 (macGrp sqrMacC 1)))

def crossV (mr : Prog isa) : Prog isa :=
  .seq (.block [.addi .t3 .a3 0, .addi .a1 .t0 (-1), .addi .t2 .a5 8])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .li .s1 0, .addi .a0 .t3 8, .addi .t4 .t2 0,
        .addi .t5 .a1 0])
      (.seq mr (.block [.store .d .s1 .t4 0, .addi .t3 .t3 8, .addi .t2 .t2 16,
        .addi .a1 .a1 (-1)])))
      (.nonzero .a1))

def reduceV (mr : Prog isa) : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t2 .t0 0, .li .a1 0])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .mul .s0 .s0 .t1, .li .s1 0, .addi .a0 .a7 0,
        .addi .t4 .t3 0, .addi .t5 .t0 0])
      (.seq mr (.block redTop)))
      (.nonzero .t2))

/-- Product scanning of the cross products: column `k` (1 to `2 w - 3`) is
`Σ_{i<j, i+j=k} aᵢ aⱼ` plus the carry, accumulated in `s0`, `s1`, `s5`, its low word stored at
word `k` of `T` (`t2`). -/
def prod : List Instr :=
  [.load .d .s2 .t3 0, .load .d .s3 .t4 0, .mul .s4 .s2 .s3, .mulhu .s3 .s2 .s3,
    .add .s0 .s0 .s4, .sltu .s4 .s0 .s4, .add .s3 .s3 .s4, .add .s1 .s1 .s3, .sltu .s4 .s1 .s3,
    .add .s5 .s5 .s4, .addi .t3 .t3 8, .addi .t4 .t4 (-8)]

def colPost : List Instr :=
  [.store .d .s0 .t2 0, .addi .s0 .s1 0, .addi .s1 .s5 0, .li .s5 0, .addi .t2 .t2 8,
    .addi .a0 .a0 8, .addi .a1 .a1 1, .addi .t6 .t6 (-1)]

def crossComba : Prog isa :=
  .seq (.block [.li .s0 0, .li .s1 0, .li .s5 0, .addi .t2 .a5 8, .li .a1 1, .addi .a0 .a3 8,
      .addi .t6 .t0 (-1)])
    (.seq (.loop (.seq (.block [.addi .t3 .a3 0, .addi .t4 .a0 0, .addi .t5 .a1 1,
          .shift .srl .d .t5 .t5 1])
        (.seq (countLoop .t5 prod) (.block colPost))) (.nonzero .t6))
      (.seq (.block [.addi .a0 .a3 8, .shift .sll .d .s6 .t0 3, .add .s6 .s6 .a3, .addi .s6 .s6 (-8),
          .addi .t6 .t0 (-2)])
        (.seq (.ite (.zero .t6) (.block [])
          (.loop (.seq (.block [.addi .t3 .a0 0, .addi .t4 .s6 0, .addi .t5 .a1 1,
              .shift .srl .d .t5 .t5 1, .sub .s2 .a1 .t0, .addi .s2 .s2 1, .sub .t5 .t5 .s2])
            (.seq (countLoop .t5 prod) (.block colPost))) (.nonzero .t6)))
          (.block [.store .d .s0 .t2 0, .store .d .s1 .t2 8]))))

def sqrW (cr : Prog isa) (mr : Prog isa) : Prog isa :=
  .seq zeroT (.seq cr (.seq diag (.seq (reduceV mr)
    (.seq (.block finishPre) (.seq subMod64 (.seq selectAcc64 (.block finishPost)))))))

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}(ws: *mut u64, w: usize, count: usize) " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto8

open Proto8 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto8.rs"
  let fns : List (String × Prog isa) := [
    ("vg_p8_mul_base", mulLoop tail),
    ("vg_p8_mul_c", mulLoop tailC),
    ("vg_p8_mul_h", mulLoop (tailH fiosHead fiosStep stepH)),
    ("vg_p8_mul_hc", mulLoop (tailH fiosHeadC fiosStepC stepHC)),
    ("vg_p8_sqr_base", sqrLoop sqrTail),
    ("vg_p8_sqr_cu8", sqrLoop (sqrW (crossV (macRunV sqrMacC 8)) (macRunV sqrMacC 8))),
    ("vg_p8_sqr_h", sqrLoop (sqrW (crossV macRunH) macRunH)),
    ("vg_p8_sqr_comba", sqrLoop (sqrW crossComba macRunH)),
    ("vg_p8_sqr_combab", sqrLoop (sqrW crossComba (macRunV sqrMacC 8)))]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    String.join (fns.map fun (n, c) => emitFn n c))
