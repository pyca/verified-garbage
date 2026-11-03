import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-! Throwaway: prints claude/great-bohr-v2olhq-rsa-precomp's proven `precompute`, to
check under qemu against main's (Proto16's base). Never in a PR. -/

open VG VG.RISCV64

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto16b.rs"
  IO.FS.writeFile out ("//! The proven precompute, for a local check only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    emitFn "vg_p16_precompute_proven"
      "(pre: *mut u64, pre_len: usize, n: *const u8, n_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"
      VG.Impl.Bignum.RISCV64.Precompute.precompute)
