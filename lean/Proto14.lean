import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Rsa.RISCV64.CheckKey
import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues

/-! Throwaway, unproven: the RSA key operations' fixed-iteration division (`Div.divK`)
on the divisor's words only (`k = ⌈p_len / 8⌉`, public) instead of `n`'s, and its
word pass with a shorter carry chain (the divisor's word added first, the carry
last). `vg_rsa_check_key` (#4091's) and `vg_rsa_crt_values` with each, next to the
current ones. Printed for timing on RISE and local checks under qemu. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div

namespace Proto14

/-- `passBody` with the carry added last: `u = 2 r + c + (d ⊕ mask)` as
`(2 r + c) + (d ⊕ mask)`, its carry in `a5`, then `+ c'`, its carry or'ed in. -/
def passShort : List Instr :=
  [.load .d .t5 .t0 0, .shift .sll .d .t6 .t5 1, .logic .or .t6 .t6 .t3, .shift .srl .d .t3 .t5 63,
    .load .d .t5 .t1 0, .logic .xor .t5 .t5 .a4, .add .t6 .t6 .t5, .sltu .a5 .t6 .t5,
    .add .t6 .t6 .t4, .sltu .t4 .t6 .t4, .logic .or .t4 .t4 .a5, .store .d .t6 .t0 0,
    .addi .t0 .t0 8, .addi .t1 .t1 8]

def stepKB (body : List Instr) (q r d : Nat) (k : Reg) : Prog isa :=
  .seq (.block (qword q ++ [.load .d .t5 .t2 0, .shift .srl .d .t3 .t5 63] ++ ptr .t0 r ++ ptr .t1 d ++
      [.logicImm .and .t4 .a4 1, .addi .t2 k 1]))
    (.seq (countLoop .t2 body)
      (.block ([.shift .srl .d .t5 .t6 63, .addi .a4 .t5 (-1), .logicImm .and .a5 .a4 1] ++ qword q ++
        [.load .d .t5 .t2 0, .shift .sll .d .t5 .t5 1, .logic .or .t5 .t5 .a5, .store .d .t5 .t2 0,
          .addi .s7 .s7 (-1)])))

def divKB (body : List Instr) (q r d : Nat) (k : Reg) : Prog isa :=
  .seq (init r) (.seq (.loop (stepKB body q r d k) (.nonzero .s7)) (fixK r d k))

/-- `s8 := ⌈len / 8⌉`. -/
def words (len : Reg) : List Instr := [.addi .s8 len 7, .shift .srl .d .s8 .s8 3]

/-- A variant: the body, and whether the width is the divisor's (`s8` from its length)
or `n`'s (`s9`). -/
structure V where
  body : List Instr
  narrow : Bool

def dv (v : V) (q r d : Nat) (len : Reg) : Prog isa :=
  if v.narrow then .seq (.block (words len)) (divKB v.body q r d .s8) else divKB v.body q r d .s9

/-- `dv` with the width already in `k` (narrow) or `n`'s. -/
def dvK (v : V) (q r d : Nat) (k : Reg) : Prog isa :=
  if v.narrow then divKB v.body q r d k else divKB v.body q r d .s9

/-! ## `vg_rsa_check_key` -/

section
open VG.Impl.Rsa.RISCV64.KeyCheck
/-- `p_len` (`s4`) does not survive `tail`, which writes `s0`–`s4`: `⌈p_len / 8⌉` is
kept in `s5` (`q`'s pointer, dead after the loads), which nothing after the loads writes. -/
def dChecksV (v : V) : List (Prog isa) :=
  ltA aD aN ++ [copy aVQ aD, copy aVD aM1, dvK v aVQ aVR aVD .s5] ++ eqA aVR aDP ++
    [copy aVQ aD, copy aVD aM2, dv v aVQ aVR aVD .s6] ++ eqA aVR aDQ

def keyV (v : V) : Prog isa :=
  fn 64 VG.Impl.Rsa.RISCV64.CheckKey.moves VG.Impl.Rsa.RISCV64.CheckKey.loads ([.block [.addi .s5 .s4 7, .shift .srl .d .s5 .s5 3]] ++ start ++ crtChecks ++ dChecksV v)
end

/-! ## `vg_rsa_crt_values` -/

section
open VG.Impl.Rsa.RISCV64.CrtValues
def checksV (v : V) : Prog isa := seqs [
  copy aDD aP, .block (bitOf sPodd aP), dv v aDQ aDR aDD .s4, eqS sE1 aDQ aQ, eqS sE2 aDR aZero]

def dPartsV (v : V) : Prog isa := seqs [
  copy aDQ aD, copy aDD aP, .block (clrLow aDD), dv v aDQ aDR2 aDD .s4,
  copy aDQ aD, copy aDD aQ, .block (clrLow aDD), dv v aDQ aDR3 aDD .s6]

def crtV (v : V) : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) (seqs [setup, loads, seqs [checksV v, invPart, dPartsV v], stores]) fail) (.block restore)))
end

def vA : V := ⟨passBody, true⟩
def vB : V := ⟨passShort, false⟩
def vC : V := ⟨passShort, true⟩

def sigKey : String :=
  "(n: *const u8, n_len: usize, e: *const u8, e_len: usize, d: *const u8, d_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"
def sigCrt : String :=
  "(dp: *mut u8, dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize, n: *const u8, n_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, d: *const u8, d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto14

open Proto14 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto14.rs"
  let fns : List (String × String × Prog isa) := [
    ("vg_p14_check_key_base", sigKey, VG.Impl.Rsa.RISCV64.CheckKey.code),
    ("vg_p14_check_key_a", sigKey, keyV vA),
    ("vg_p14_check_key_b", sigKey, keyV vB),
    ("vg_p14_check_key_c", sigKey, keyV vC),
    ("vg_p14_crt_values_base", sigCrt, VG.Impl.Rsa.RISCV64.CrtValues.code),
    ("vg_p14_crt_values_a", sigCrt, crtV vA),
    ("vg_p14_crt_values_b", sigCrt, crtV vB),
    ("vg_p14_crt_values_c", sigCrt, crtV vC)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, s, c) => emitFn n s c))
