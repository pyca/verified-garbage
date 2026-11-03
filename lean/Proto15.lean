import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet
import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues

/-! Throwaway, unproven: `vg_rsa_crt_values` with `p q = n` by `mulLow` when `p_len + q_len ≤ 8 w`. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div

namespace Proto15

section
open VG.Impl.Rsa.RISCV64.CrtValues

/-- When `p_len + q_len ≤ 8 w`, `p q < 2^(64 w)`: `p q = n` is `p q mod 2^(64 w) = n`
(`mulLow`), with `a2`, `a3`, `a6` (which it writes) kept in `s1`, `s3`, `s5`, dead
after the loads. Else the division. -/
def fast : Prog isa := seqs [
  .block (bitOf sPodd aP ++ [mov .s1 .a2, mov .s3 .a3, mov .s5 .a6]),
  VG.Impl.Rsa.RISCV64.RecoverDet.mulLow aDR aP aQ,
  .block [mov .a2 .s1, mov .a3 .s3, mov .a6 .s5],
  eqS sE1 aDR aDQ, .block [.li .t5 1, .store .d .t5 .s11 sE2]]

def checksF : Prog isa :=
  .seq (.block [.add .t5 .s4 .s6, .shift .sll .d .t6 .s9 3, .sltu .t5 .t6 .t5]) (.ite (.zero .t5) fast checks)

def crtF : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) (seqs [setup, loads, seqs [checksF, invPart, dParts], stores]) fail) (.block restore)))

/-- The fast path forced off, to check the slow one is still right. -/
def crtS : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) (seqs [setup, loads, seqs [checks, invPart, dParts], stores]) fail) (.block restore)))
end

def sigCrt : String :=
  "(dp: *mut u8, dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize, n: *const u8, n_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, d: *const u8, d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto15

open Proto15 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto15.rs"
  let fns : List (String × String × Prog isa) := [
    ("vg_p15_crt_values_base", sigCrt, VG.Impl.Rsa.RISCV64.CrtValues.code),
    ("vg_p15_crt_values_f", sigCrt, crtF)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, s, c) => emitFn n s c))
