import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Key

/-! Throwaway, unproven: prints the RISC-V `vg_rsa_keygen_key` with its inverses
by the batched divsteps (`InvBatch`), for qemu checks and RISE timing. Never in
a PR. -/

open VG VG.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Key VG.Impl.Rsa.RISCV64.Keys

namespace Proto10

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "rsa_proto10") "super" ++ "}\n"

end Proto10

def main (args : List String) : IO Unit := do
  let sig := "(n: *mut u8, n_len: usize, d: *mut u8, d_len: usize, p: *mut u8, p_len: usize, q: *mut u8, q_len: usize, dp: *mut u8, dp_len: usize, dq: *mut u8, dq_len: usize, qinv: *mut u8, qinv_len: usize, e: *const u8, e_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"
  IO.FS.writeFile (args.headD "rsa_proto10.rs") ("//! Unproven prototype, for local checks only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    Proto10.emitFn "vg_rsa_keygen_key_ib_proto" sig VG.Impl.RsaKeyGen.RISCV64.Key.code)
