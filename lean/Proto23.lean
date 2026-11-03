import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.Crt

/-! Throwaway, unproven: `vg_rsa_private_crt` with pieces left out, to time the split. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp output)
open VG.Impl.Bignum.RISCV64.Crt

namespace Proto23

/-- `window` without the table scan. -/
def windowNoSel : Prog isa :=
  .seq (ModExp.sqrOp 6 6 5) (.seq (ModExp.sqrOp 6 6 5) (.seq (ModExp.sqrOp 6 6 5) (.seq (ModExp.sqrOp 6 6 5)
    (.seq (.block [.shift .srl .d .a1 .s7 60]) (.seq (montOp 6 6 5)
      (.block [.shift .sll .d .s7 .s7 4]))))))
def byteWinNoSel : Prog isa :=
  .seq (.block [.load .b .s7 .s9 0, .shift .sll .d .s7 .s7 56, .addi .s9 .s9 1]) (.seq windowNoSel windowNoSel)
def powWinNoSel : Prog isa :=
  .seq ModExp.table (.seq (.loop (.seq byteWinNoSel (.block [.addi .s10 .s10 (-1)])) (.nonzero .s10)) (montOp 4 6 7))

def powerWith (pw : Prog isa) (r2 red : Bool) (xj oD oLen : Nat) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ xb .t4 xj)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
  (.seq (if r2 then r2Prime 4 else .block []) (.seq (if red then reduceIn else .block [])
  (.seq (.block [.load .d .s9 .s6 oD, .load .d .s10 .s6 oLen]) pw)))))

def recombinePWith (r2 red : Bool) : Prog isa :=
  .seq (.block [.load .d .s10 .s6 oQLen])
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3)) (.seq (if r2 then r2Prime 5 else .block [])
  (.seq (.block (base .t3 7 ++ base .t4 1)) (.seq copyN
  (.seq (.block (xb .s9 1)) (.seq (if red then ModArith.reduce64 else .block [])
  (.seq (.block (base .t3 4 ++ [.add .t3 .t3 .s5, .addi .t3 .t3 (-16), .li .s0 0, .store .d .s0 .t3 0] ++
      base .a5 4 ++ base .a6 3 ++ base .a7 1))
  (.seq subMod64 (.seq (.block ([.addi .a7 .ra 0] ++ base .t3 3 ++ base .t4 0)) (.seq ModArith.addMask64
  (.seq (.block (base .t3 6 ++ xb .t4 7)) (.seq copyN
  (.seq (montOp 5 3 6) (montOp 4 5 7))))))))))))))

def crtWith (pw : Prog isa) (r2p red r2re redre : Bool) : Prog isa :=
  .seq (.block (save ++ args ++ setupX)) (.seq loadX (.seq checks (.seq loadIn
  (.seq (.block (setupP oBP oPLen)) (.seq (powerWith pw r2p red 4 oDP oPLen)
  (.seq (.block (setupP oBQ oQLen)) (.seq (powerWith pw r2p red 5 oDQ oQLen) (.seq exportM2
  (.seq (.block (setupP oBP oPLen)) (.seq (recombinePWith r2re redre) (.seq recombineX
  (.seq (.block [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut, .load .d .s11 .s6 oNLen,
      .load .d .s9 .s6 oMask])
    (.seq output (.block restore))))))))))))))

def sig : String :=
  "(out: *mut u8, out_len: usize, n: *const u8, n_len: usize, input: *const u8, input_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto23

open Proto23 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto23.rs"
  let pw := ModExp.powWin
  let fns : List (String × Prog isa) := [
    ("vg_p23_base", VG.Impl.Bignum.RISCV64.Crt.crt),
    ("vg_p23_same", crtWith pw true true true true),
    ("vg_p23_nor2re", crtWith pw true true false true),
    ("vg_p23_nored64", crtWith pw true true true false),
    ("vg_p23_nobitserial", crtWith pw false true false false),
    ("vg_p23_nosel", crtWith powWinNoSel true true true true)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, c) => emitFn n c))
