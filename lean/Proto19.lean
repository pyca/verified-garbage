import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Rsa.RISCV64.CrtValues

/-! Throwaway, unproven: `vg_rsa_crt_values` with pieces left out, to time the split. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div
open VG.Impl.Rsa.RISCV64.CrtValues

namespace Proto19

def withArith (a : Prog isa) : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) (seqs [setup, loads, a, stores]) fail) (.block restore)))

/-- Without the inverse (its setup and checks kept). -/
def invPartNoInv : Prog isa := seqs (invSetup ++ [
  eqS sE3 1 aOne,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3 ++ mask),
  storeBytes 3 .a6 .s4])

def noDiv : Prog isa := withArith (seqs [checks, invPart])
def noInv : Prog isa := withArith (seqs [checks, invPartNoInv, dParts])
def onlyChecks : Prog isa := withArith (seqs [checks, invPartNoInv])

def sigCrt : String :=
  "(dp: *mut u8, dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize, n: *const u8, n_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, d: *const u8, d_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto19

open Proto19 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto19.rs"
  let fns : List (String × String × Prog isa) := [
    ("vg_p19_crt_base", sigCrt, VG.Impl.Rsa.RISCV64.CrtValues.code),
    ("vg_p19_crt_nodiv", sigCrt, noDiv),
    ("vg_p19_crt_noinv", sigCrt, noInv),
    ("vg_p19_crt_checks", sigCrt, onlyChecks)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, s, c) => emitFn n s c))
