import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues

/-! Throwaway, unproven: `vg_rsa_crt_values` whose inverse's `mred` adds `m` only
where the quotient is negative (its top digit's sign), so one conditional
subtraction (not two) reduces it into `[0, m)`. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.InvBatch
open VG.Impl.Rsa.RISCV64.CrtValues

namespace Proto21

def mred' (t o : Nat) : Prog isa := seqs [
  .block (ptr .t0 t ++ ldW .t6 wIv ++ [.load .w .t5 .t0 0, .mul .a5 .t5 .t6, .shift .sll .d .a5 .a5 32,
    .shift .srl .d .a5 .a5 32]),
  mac t t aMz cntN1,
  .block [.load .w .t5 .t0 0, .add .t5 .t5 .t4, .store .w .t5 .t0 0, .shift .srl .d .a5 .t5 31,
    .logicImm .and .a5 .a5 1],
  .block (ptr .t0 aT3 ++ ptr .t1 t ++ ptr .t2 aMz ++ [.addi .t1 .t1 4] ++ cntN1 ++ [.li .t4 0]),
  countLoop .t3 macBody,
  csub o aT3 t]

def updateAB' : Prog isa := seqs [lin wU wV aT1 aA aB, lin wQ wR aT2 aA aB, mred' aT1 aA, mred' aT2 aB]
def update' : Prog isa := .seq updateG updateAB'
def batch' : Prog isa := seqs [.block (start ++ wsteps 30 ++ VG.Impl.Rsa.RISCV64.InvBatch.save), update', .block [.addi .s7 .s7 (-1)]]
def inverse' : Prog isa := seqs [init, .loop batch' (.nonzero .s7), normalize, doublings, finish]

def invPart' : Prog isa := seqs (invSetup ++ [
  inverse', eqS sE3 1 aOne,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3 ++ mask),
  storeBytes 3 .a6 .s4])

def code' : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) (seqs [setup, loads, seqs [checks, invPart', dParts], stores]) fail) (.block restore)))

def sigCrt : String :=
  "(dp: *mut u8, dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize, n: *const u8, n_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, d: *const u8, d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto21

open Proto21 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto21.rs"
  let fns : List (String × String × Prog isa) := [
    ("vg_p21_crt_base", sigCrt, VG.Impl.Rsa.RISCV64.CrtValues.code),
    ("vg_p21_crt_inv1", sigCrt, code')]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, s, c) => emitFn n s c))
