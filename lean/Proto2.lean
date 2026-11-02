import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Rsa.RISCV64.Priv

open VG VG.RISCV64

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "rsa_proto2") "super" ++ "}\n"

def p8 (ns : List String) : String := ", ".intercalate (ns.map fun n => s!"{n}: *const u8, {n}_len: usize")

def main (args : List String) : IO Unit := do
  let crtSig := s!"(out: *mut u8, out_len: usize, {p8 ["n", "input", "p", "q", "dp", "dq", "qinv"]}, scratch: *mut u64, scratch_len: usize) -> u32"
  let privSig := s!"(out: *mut u8, out_len: usize, {p8 ["n", "e", "input", "p", "q", "dp", "dq", "qinv"]}, scratch: *mut u64, scratch_len: usize) -> u32"
  let preSig := "(pre: *mut u64, pre_len: usize, n: *const u8, n_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"
  let pubSig := "(out: *mut u8, out_len: usize, pre: *const u64, pre_len: usize, e: *const u8, e_len: usize, input: *const u8, input_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"
  IO.FS.writeFile (args.headD "rsa_proto2.rs") ("//! Unproven prototype, for local checks only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    emitFn "vg_rsa_private_crt" crtSig Impl.Bignum.RISCV64.Crt.crt ++
    emitFn "vg_rsa_public_precompute" preSig Impl.Bignum.RISCV64.Precompute.precompute ++
    emitFn "vg_rsa_public_precomputed_checked" pubSig Impl.Bignum.RISCV64.PublicChecked.publicChecked ++
    emitFn "vg_rsa_private_checked" privSig Impl.Rsa.RISCV64.Priv.code)
