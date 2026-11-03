import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Bignum.RISCV64.Crt

/-! Throwaway, unproven: `vg_rsa_private_crt` with windows of 5 or 6 bits. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp output one)
open VG.Impl.Bignum.RISCV64.Crt
open VG.Impl.Bignum.RISCV64.ModExp (sqrOp ones copy entry toEntry isDigit)

namespace Proto24

/-- Table of `2^k` entries. -/
def table (k : Nat) : Prog isa :=
  .seq one (.seq (montOp 8 1 7) (.seq (montOp 9 4 1) (.seq (copy 6 9) (.seq (.block [.li .s7 2])
    (.seq (.loop (.seq (montOp 6 6 9) (.seq toEntry
        (.block [.addi .s7 .s7 1, .addi .t2 .s7 (-((2 ^ k : Nat) : Int))]))) (.nonzero .t2))
      (copy 6 8))))))

def select (k : Nat) : Prog isa :=
  .seq (.block [.li .s8 0])
    (.loop (.seq (.block (isDigit ++ entry .a5 .s8 ++ base .a6 5 ++ base .a2 3)) (.seq selectAcc64
      (.seq (.block ([.addi .s8 .s8 1] ++ isDigit ++ entry .a5 .s8 ++ base .a6 3 ++ base .a2 5)) (.seq selectAcc64
        (.block [.addi .s8 .s8 1, .addi .t2 .s8 (-((2 ^ k : Nat) : Int))]))))) (.nonzero .t2))

def sqrs : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (sqrOp 6 6 5) (sqrs n)

/-- One window of `k` bits at the top of `s7`. -/
def window (k : Nat) : Prog isa :=
  .seq (sqrs k) (.seq (.block [.shift .srl .d .a1 .s7 (64 - k)]) (.seq (select k) (.seq (montOp 6 6 5)
    (.block [.shift .sll .d .s7 .s7 k]))))

def windows : Nat → Nat → Prog isa
  | _, 0 => .block []
  | k, n + 1 => .seq (window k) (windows k n)

/-- A group of `g` bytes (`a1` of them at `s9`, the rest leading zeros) into the top of `s7`. -/
def loadGroup (g : Nat) : Prog isa :=
  .seq (.block [.li .s7 0])
    (.seq (.loop (.block [.load .b .t2 .s9 0, .shift .sll .d .s7 .s7 8, .logic .or .s7 .s7 .t2, .addi .s9 .s9 1,
        .addi .a1 .a1 (-1)]) (.nonzero .a1))
      (.block [.shift .sll .d .s7 .s7 (64 - 8 * g)]))

/-- `x^d mod m` with windows of `k` bits over groups of `g` bytes (`g·8 = n·k`), `s10` the exponent's bytes
at `s9`; `mulC`, `shC`: `⌈len/g⌉ = ((len + g - 1) · mulC) >> shC`. -/
def powWin (k g n : Nat) (mulC shC : Nat) : Prog isa :=
  .seq (table k)
  -- groups `t2 = ⌈len/g⌉` by subtraction; the first group's bytes `a1 = len - g (t2 - 1)`
  (.seq (.block [.li .t2 0, .addi .t3 .s10 0])
  (.seq (.loop (.block [.addi .t3 .t3 (-(g : Int)), .addi .t2 .t2 1, .addi .t4 .t3 (-1),
      .shift .srl .d .t4 .t4 63, .logicImm .xor .t4 .t4 1]) (.nonzero .t4))
  (.seq (.block [.addi .a1 .t3 (g : Int), .addi .s10 .t2 0])
  (.seq (.loop (.seq (loadGroup g) (.seq (windows k n) (.block [.li .a1 (g : Int), .addi .s10 .s10 (-1)])))
      (.nonzero .s10))
    (montOp 4 6 7)))))

def powerWith (pw : Prog isa) (xj oD oLen : Nat) : Prog isa :=
  .seq (.block ([.addi .t3 .a7 0] ++ xb .t4 xj)) (.seq copyN
  (.seq (.block (Precompute.minv ++ base .a2 1 ++ base .a5 2 ++ base .a6 3))
  (.seq (r2Prime 4) (.seq reduceIn
  (.seq (.block [.load .d .s9 .s6 oD, .load .d .s10 .s6 oLen]) pw)))))

/-- `setupX` with `8 + 2^k` arrays in each prime's space: `mulA` and `shA` with `8 + 2^k = 8 (1 + 2^shA)`... given as shift pair. -/
def setupXN (sh : Nat) : List Instr :=
  [.addi .t2 .a3 7, .shift .srl .d .t2 .t2 3, .shift .sll .d .t2 .t2 1] ++ area .s6 ++
    [.addi .s11 .s5 0, .shift .sll .d .t4 .s5 3, .add .t4 .a7 .t4, .store .d .t4 .s6 oBP,
      .load .d .t3 .s6 oPLen] ++ words .t2 .t3 ++
    [.shift .sll .d .t3 .t2 3, .addi .t3 .t3 16, .shift .sll .d .t3 .t3 3, .shift .sll .d .t5 .t3 sh, .add .t3 .t3 .t5,
      .addi .t3 .t3 hdrBytes, .add .t4 .t4 .t3, .store .d .t4 .s6 oBQ]

def crtWith (sx : List Instr) (pw : Prog isa) : Prog isa :=
  .seq (.block (save ++ args ++ sx)) (.seq loadX (.seq checks (.seq loadIn
  (.seq (.block (setupP oBP oPLen)) (.seq (powerWith pw 4 oDP oPLen)
  (.seq (.block (setupP oBQ oQLen)) (.seq (powerWith pw 5 oDQ oQLen) (.seq exportM2
  (.seq (.block (setupP oBP oPLen)) (.seq recombineP (.seq recombineX
  (.seq (.block [.addi .a7 .s6 hdrBytes, .addi .s5 .s11 0, .load .d .s10 .s6 oOut, .load .d .s11 .s6 oNLen,
      .load .d .s9 .s6 oMask])
    (.seq output (.block restore))))))))))))))

def sig : String :=
  "(out: *mut u8, out_len: usize, n: *const u8, n_len: usize, input: *const u8, input_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto24

open Proto24 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto24.rs"
  let fns : List (String × Prog isa) := [
    ("vg_p24_base", VG.Impl.Bignum.RISCV64.Crt.crt),
    -- 8 + 16 = 24 = 8 · 3: setupX's own (t3·8, ·3) is (t5 = 2 t3, t3 += t5): sh = 1
    ("vg_p24_w4", crtWith (setupXN 1) (powWin 4 1 2 1 0)),
    -- 8 + 32 = 40 = 8 · 5: sh = 2; groups of 5 bytes: ⌈len/5⌉ = ((len+4)·52429) >> 18
    ("vg_p24_w5", crtWith (setupXN 2) (powWin 5 5 8 52429 18)),
    -- 8 + 64 = 72 = 8 · 9: sh = 3; groups of 3 bytes: ⌈len/3⌉ = ((len+2)·43691) >> 17
    ("vg_p24_w6", crtWith (setupXN 3) (powWin 6 3 4 43691 17))]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, c) => emitFn n c))
