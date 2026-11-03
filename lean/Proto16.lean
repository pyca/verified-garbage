import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr

/-! Throwaway, unproven: `vg_rsa_public_precompute` with the doublings started at
`n`'s top bit (`2^(b - 1)`, `b` its bit length) and/or the six squares by `sqrTail`.
Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Precompute

namespace Proto16

/-- `a1 := z`, the leading zeros of `n`'s top word (not zero), by shifting it
left until its top bit is set. -/
def lz : Prog isa :=
  .seq (.block [.shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .s0 .t3 0,
      .li .a1 0, .shift .srl .d .s1 .s0 63, .logicImm .xor .s1 .s1 1])
    (.ite (.zero .s1) (.block [])
      (.loop (.block [.shift .sll .d .s0 .s0 1, .addi .a1 .a1 1, .shift .srl .d .s1 .s0 63,
        .logicImm .xor .s1 .s1 1]) (.nonzero .s1)))

/-- `x := 2^(64 (w - 1) + 63 - z)` (below `n`), then `w + 1 + z` doublings:
`2^w R mod n`. -/
def hiDblTop : Prog isa :=
  .seq lz (.seq (.block [.addi .t3 .a2 0]) (.seq zeroWords
    (.seq (.block [.shift .sll .d .t3 .t0 3, .add .t3 .t3 .a2, .addi .t3 .t3 (-8), .li .s1 63,
        .sub .s1 .s1 .a1, .li .s0 1, .shiftReg .sll .d .s0 .s0 .s1, .store .d .s0 .t3 0,
        .add .a1 .a1 .t0, .addi .a1 .a1 1])
      (.loop (.seq doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)))))

/-- `x := x² R⁻¹ mod n` by `sqrTail`, `T` in arrays 2–3, its temporary array 4. -/
def sq1 : Prog isa := .seq (.block [.addi .a3 .a2 0]) sqrTail

/-- `a6` at array 4, then six `sq1`. -/
def squaresS : Prog isa :=
  .seq (.block [.shift .sll .d .s0 .t0 3, .addi .s0 .s0 16, .add .a6 .a6 .s0])
    (.seq sq1 (.seq sq1 (.seq sq1 (.seq sq1 (.seq sq1 sq1)))))

def mk (dbl sq : Prog isa) : Prog isa :=
  let r2' : Prog isa := .seq dbl (.seq (.block minv) sq)
  let core' : Prog isa :=
    .seq loadN (.seq check (.ite (.zero .s0) (.seq r2' (.seq write (.block [.li .a0 1])))
      (.seq zeroPre (.block [.li .a0 0]))))
  .seq (.block (save ++ setup)) (.seq core' (.block restore))

def sig : String :=
  "(pre: *mut u64, pre_len: usize, n: *const u8, n_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto16

open Proto16 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto16.rs"
  let fns : List (String × String × Prog isa) := [
    ("vg_p16_precompute_base", sig, precompute),
    ("vg_p16_precompute_top", sig, mk hiDblTop r2Squares),
    ("vg_p16_precompute_sqr", sig, mk r2HiDbl squaresS),
    ("vg_p16_precompute_both", sig, mk hiDblTop squaresS)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc)]\n" ++
    String.join (fns.map fun (n, s, c) => emitFn n s c))
