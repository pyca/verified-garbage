import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Impl.Rsa.RISCV64.CheckCrtKey
import VerifiedGarbage.Impl.Rsa.RISCV64.CheckKey
import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet
import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-! Throwaway, unproven: `vg_rsa_check_crt_key` and `vg_rsa_check_key` with `p q = n` and
`q qInv ≡ 1 (mod p)` checked by Montgomery products (`MontMul.tail`, its arrays 0–7 at the
key working space's arrays 16–23) and the low product, instead of the bit-serial division
of `n` by `p` and the bit-serial `mulMod` over `q`'s bits. Printed for timing on RISE and
local checks under qemu, next to main's two functions. Never in a PR. -/

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.KeyCheck

namespace Proto13

/-- `tail`'s arrays 0 (`m`), 2 (the accumulator) and 3 (its temporary), and the operands. -/
def mM : Nat := 16
def mA : Nat := 17
def mT : Nat := 18
def mTmp : Nat := 19
def mB : Nat := 20
def mO : Nat := 21
def mO2 : Nat := 22

/-- `[o] := [a] [b] R⁻¹ mod m`, `m` at array 16: `-m⁻¹ mod 2⁶⁴` into `t1` by
`Precompute.minv`, `w` into `t0` and the pointers, then `tail`. -/
def mont (o a b : Nat) : Prog isa :=
  .seq (.block (ptr .a7 mM ++ Precompute.minv ++ [mov .t0 .s9] ++ ptr .a5 mT ++ ptr .a6 mTmp ++
    ptr .a2 o ++ ptr .a3 a ++ ptr .a4 b)) tail

/-- `m := p | 1 | 2 [p < 2]`: odd and at least 3, and `p` when `p` is odd and at least 3. -/
def setM : List (Prog isa) :=
  [copy mM aP, .block (ptr .t0 mO ++ [.li .t5 2, .store .d .t5 .t0 0]), sub3 aW aP mO,
    .block (ptr .t0 mM ++ [.load .d .t5 .t0 0, .shift .sll .d .t6 .t4 1, .logic .or .t5 .t5 .t6,
      .logicImm .or .t5 .t5 1, .store .d .t5 .t0 0])]

/-- `p | n` (`n R⁻¹ mod m = 0`) and `p q ≡ n (mod 2^(64 w))`: with `p` odd, `p q = n`. -/
def pqChecks : List (Prog isa) :=
  setM ++ [copy mA aN, copy mB aZ, .block (setOne mB), mont mO mA mB] ++ eqA mO aZ ++
    [copy mO2 aZ, VG.Impl.Rsa.RISCV64.RecoverDet.mulLow mO2 aP aQ] ++ eqA mO2 aN

/-- `qInv < p`, then `q qInv' R⁻¹ ≡ R⁻¹ (mod m)`, `qInv'` := `qInv` if `qInv < p`, else 0. -/
def qiChecks : List (Prog isa) :=
  ltA aQI aP ++ [sel mB aZ aQI sF, copy mA aQ, mont mO mA mB, copy mA aOne, mont mO2 mA mA,
    eqS sF mO mO2, .block acc]

def start' : List (Prog isa) := [.block (setOne aOne ++ bitOf sMask aP)]

def crtChecks' : List (Prog isa) := pqChecks ++ qiChecks ++
  [copy aM1 aP, .block (clrLow aM1), copy aM2 aQ, .block (clrLow aM2)] ++
  ltA aDP aM1 ++ mulA aE aDP aM1 cnt33 ++ eqA aA aOne ++
  ltA aDQ aM2 ++ mulA aE aDQ aM2 cnt33 ++ eqA aA aOne

def crtNew : Prog isa := fn 48 VG.Impl.Rsa.RISCV64.CheckCrtKey.moves VG.Impl.Rsa.RISCV64.CheckCrtKey.loads (start' ++ crtChecks')
def keyNew : Prog isa := fn 64 VG.Impl.Rsa.RISCV64.CheckKey.moves VG.Impl.Rsa.RISCV64.CheckKey.loads (start' ++ crtChecks' ++ dChecks)

def sigCrt : String :=
  "(n: *const u8, n_len: usize, e: *const u8, e_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"
def sigKey : String :=
  "(n: *const u8, n_len: usize, e: *const u8, e_len: usize, d: *const u8, d_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize, dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize, qinv: *const u8, qinv_len: usize, scratch: *mut u64, scratch_len: usize) -> u32"

def emitFn (name sig : String) (code : Prog isa) : String :=
  let lines := RISCV64.target.printer.function code
  s!"#[unsafe(naked)]\npub unsafe extern \"C\" fn {name}{sig} " ++ "{\n" ++
    Rust.asmOf RISCV64.target (Rust.bodyLines RISCV64.target [] lines) (fun _ => "") "super" ++ "}\n"

end Proto13

open Proto13 in
def main (args : List String) : IO Unit := do
  let out := args.headD "rsa_proto13.rs"
  let fns : List (String × String × Prog isa) := [
    ("vg_p13_check_crt_key_base", sigCrt, VG.Impl.Rsa.RISCV64.CheckCrtKey.code),
    ("vg_p13_check_crt_key_new", sigCrt, crtNew),
    ("vg_p13_check_key_base", sigKey, VG.Impl.Rsa.RISCV64.CheckKey.code),
    ("vg_p13_check_key_new", sigKey, keyNew)]
  IO.FS.writeFile out ("//! Unproven prototype, for timing only.\n#![allow(clippy::missing_safety_doc, clippy::too_many_arguments)]\n" ++
    String.join (fns.map fun (n, s, c) => emitFn n s c))
