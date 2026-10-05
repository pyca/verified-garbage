import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# AArch64 condition flags: ADDS/SUBS, TST, CCMP, CSEL and CSNEG

Expected results below were produced by the same instructions in a Clang
inline-assembly probe on an Apple M1 Max (macOS 27), the flags set beforehand
with `msr nzcv` and read back with `mrs`: NZCV is written as a nibble (N in
bit 3, V in bit 0). These are instruction-semantic checks, not cryptographic
known-answer vectors.
-/

namespace VG.Test.AArch64Flags
open AArch64

def input (f : Nat) (a b : BitVec 64) : State where
  gpr r := if r = .x1 then a else if r = .x2 then b else 0xdeadbeefdeadbeef
  sp := 0x1000
  nf := f.testBit 3
  zf := f.testBit 2
  c := f.testBit 1
  vf := f.testBit 0
  mem _ := 0
  rd := []
  wr := []

def nzcv (s : State) : Nat :=
  8 * s.nf.toNat + 4 * s.zf.toNat + 2 * s.c.toNat + s.vf.toNat

def run (f : Nat) (a b : BitVec 64) (i : Instr) : Option (BitVec 64 × Nat) :=
  (exec i (input f a b)).map fun s => (s.gpr .x0, nzcv s)

def flagsAfter (f : Nat) (a b : BitVec 64) (i : Instr) : Option Nat := (exec i (input f a b)).map nzcv

#guard run 0 0x7fffffffffffffff 0x0000000000000001 (.adds .x .x0 .x1 .x2) == some (0x8000000000000000, 0x9)
#guard run 0 0xffffffffffffffff 0x0000000000000001 (.adds .x .x0 .x1 .x2) == some (0x0000000000000000, 0x6)
#guard run 0 0x8000000000000000 0x8000000000000000 (.adds .x .x0 .x1 .x2) == some (0x0000000000000000, 0x7)
#guard run 0 0x0000000000000001 0x0000000000000002 (.adds .x .x0 .x1 .x2) == some (0x0000000000000003, 0x0)
#guard run 0 0xdeadbeef7fffffff 0x0000000000000001 (.adds .w .x0 .x1 .x2) == some (0x0000000080000000, 0x9)
#guard run 0 0x00000000ffffffff 0x0000000000000001 (.adds .w .x0 .x1 .x2) == some (0x0000000000000000, 0x6)
#guard run 0 0x0000000000000005 0x0000000000000005 (.subs .x .x0 .x1 .x2) == some (0x0000000000000000, 0x6)
#guard run 0 0x0000000000000003 0x0000000000000005 (.subs .x .x0 .x1 .x2) == some (0xfffffffffffffffe, 0x8)
#guard run 0 0x8000000000000000 0x0000000000000001 (.subs .x .x0 .x1 .x2) == some (0x7fffffffffffffff, 0x3)
#guard run 0 0x0000000000000005 0x0000000000000003 (.subs .x .x0 .x1 .x2) == some (0x0000000000000002, 0x2)
#guard flagsAfter 0 0x8000000000000001 0x8000000000000000 (.tst .x .x1 .x2) == some 0x8
#guard flagsAfter 0 0x0000000000000002 0x0000000000000001 (.tst .x .x1 .x2) == some 0x4
#guard flagsAfter 0 0x0000000000000003 0x0000000000000001 (.tst .x .x1 .x2) == some 0x0
#guard flagsAfter 0 0xffffffff00000000 0xffffffff00000000 (.tst .w .x1 .x2) == some 0x4
#guard flagsAfter 0 0x0000000080000000 0x00000000ffffffff (.tst .w .x1 .x2) == some 0x8
#guard flagsAfter 0 0x0000000000000005 0 (.ccmp .x .x1 5 8 .eq) == some 0x8
#guard flagsAfter 4 0x0000000000000005 0 (.ccmp .x .x1 5 8 .eq) == some 0x6
#guard flagsAfter 4 0x0000000000000003 0 (.ccmp .x .x1 5 0 .eq) == some 0x8
#guard flagsAfter 0 0x0000000000000003 0 (.ccmp .x .x1 7 6 .ne) == some 0x8
#guard flagsAfter 8 0x0000000000000000 0 (.ccmp .x .x1 0 8 .ne) == some 0x6
#guard flagsAfter 9 0x0000000000000001 0 (.ccmp .x .x1 31 15 .ge) == some 0x8
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0xfedcba9876543210
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 0 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 1 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0x0123456789abcdef
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0xfedcba9876543210
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 2 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0x0123456789abcdef
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 3 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 4 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 5 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 6 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 7 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 8 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0xfedcba9876543210
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 9 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0x0123456789abcdef
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 10 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0xfedcba9876543210
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0x0123456789abcdef
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0xfedcba9876543210
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdef
#guard (run 11 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 12 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 13 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0xfedcba9876543210
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0x0123456789abcdef
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdf0
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 14 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdef
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .lt)).map (·.1) == some 0xfedcba9876543210
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .eq)).map (·.1) == some 0x0123456789abcdef
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .hi)).map (·.1) == some 0xfedcba9876543210
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.cselc .x .x0 .x1 .x2 .le)).map (·.1) == some 0x0123456789abcdef
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ge)).map (·.1) == some 0x0123456789abcdef
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.csneg .x .x0 .x1 .x2 .ne)).map (·.1) == some 0x0123456789abcdf0
#guard (run 15 0x0123456789abcdef 0xfedcba9876543210 (.csneg .w .x0 .x1 .x2 .lt)).map (·.1) == some 0x0000000089abcdf0

-- Encodable immediates only.
#guard exec (.ccmp .x .x1 32 0 .eq) (input 0 0 0) |>.isNone
#guard exec (.ccmp .x .x1 0 16 .eq) (input 0 0 0) |>.isNone

-- No optional CPU features, and the framework recognizes writes.
#guard Instr.requires (.tst .x .x1 .x2) == []
#guard Instr.requires (.ccmp .x .x1 0 8 .ne) == []
#guard Instr.requires (.csneg .x .x0 .x1 .x2 .lt) == []
#guard dstOf (.cselc .x .x0 .x1 .x2 .ge) == some .x0
#guard dstOf (.csneg .x .x0 .x1 .x2 .ge) == some .x0
#guard dstOf (.tst .x .x1 .x2) == none

#guard printer.instr (.tst .x .x3 .x11) == ["tst x3, x11"]
#guard printer.instr (.tst .w .x3 .x11) == ["tst w3, w11"]
#guard printer.instr (.ccmp .x .x1 0 8 .ne) == ["ccmp x1, #0, #8, ne"]
#guard printer.instr (.cselc .x .x0 .x1 .x2 .ge) == ["csel x0, x1, x2, ge"]
#guard printer.instr (.csneg .w .x0 .x1 .x2 .lt) == ["csneg w0, w1, w2, lt"]

-- The flags are not tracked, so a value selected by them is secret, and
-- instructions writing only the flags keep the public registers.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.cselc .x .x0 .x1 .x2 .ge)).map (AArch64.Taint.pub · .x0)) == some false
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.csneg .x .x0 .x1 .x2 .ge)).map (AArch64.Taint.pub · .x0)) == some false
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.tst .x .x1 .x2)).map (AArch64.Taint.pub · .x1)) == some true
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.ccmp .x .x1 0 8 .ne)).map (AArch64.Taint.pub · .x1)) == some true

end VG.Test.AArch64Flags
