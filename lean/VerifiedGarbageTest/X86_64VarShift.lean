module

import VerifiedGarbage.TCB.X86_64.Print
meta import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 shifts by a register: `shl`, `shr` and `sar` by CL, and BMI2's `shlx` and `shrx`

Each expected value was computed on an x86-64 CPU (an Intel Xeon), by the
same instruction in inline assembly, with RFLAGS set by `popfq` before it
and read by `pushfq` after it, and is compared with the model's result on
the same inputs: `shl`, `shr` and `sar rdx, cl` and `shlx` and `shrx rdx,
r8, rcx`, by counts of 0, 1, 4 and 63 and by counts the mask reduces
(64, 65, 0x100, 0x13f and 0xffffffffffffff21), with every flag set before
(and, for counts that mask to 0 or 1, every flag clear), so that each one
the instruction writes is seen to change and each one it keeps is seen to
stay. OF after a shift by a masked count other than 0 and 1 is undefined in
the model (`none`), and is not compared. This tests the transcription of
the SDM's pseudocode (the count's mask, which bit is the last shifted out,
how OF is computed, the sign fill of `sar`, and that a count of 0 changes
no flag and `shlx` and `shrx` none at all), which review of the TCB would
otherwise have to catch by eye.
-/

namespace VG.Test.X86_64VarShift

open X86_64

/-- A state with `a` in `rdx` and in `r8`, `c` in `rcx`,
`0xcccccccccccccccc` in every other register, and every flag set if `f`,
clear otherwise. -/
def s (f : Bool) (a c : BitVec 64) : State where
  gpr r := if r = .rdx then a else if r = .r8 then a else if r = .rcx then c
    else 0xcccccccccccccccc
  cf := some f
  zf := some f
  sf := some f
  of := some f
  mem _ := 0
  rd := []
  wr := []

/-- `rdx`, CF, ZF, SF and OF after `op rdx, cl` with `a` in `rdx`, `c` in
`rcx`, and every flag set if `f`, clear otherwise. -/
def cl (op : VarShiftOp) (f : Bool) (a c : BitVec 64) :
    Option (BitVec 64 × Option Bool × Option Bool × Option Bool × Option Bool) :=
  (exec (.shiftCl op .rdx) (s f a c)).map fun t => (t.gpr .rdx, t.cf, t.zf, t.sf, t.of)

def shlCl := cl .shl
def shrCl := cl .shr
def sarCl := cl .sar

#guard shlCl true 0x0 0x0 == some (0x0, some true, some true, some true, some true)
#guard shlCl false 0x0 0x0 == some (0x0, some false, some false, some false, some false)
#guard shlCl true 0x0 0x1 == some (0x0, some false, some true, some false, some false)
#guard shlCl false 0x0 0x1 == some (0x0, some false, some true, some false, some false)
#guard shlCl true 0x0 0x4 == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x0 0x3f == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x0 0x40 == some (0x0, some true, some true, some true, some true)
#guard shlCl false 0x0 0x40 == some (0x0, some false, some false, some false, some false)
#guard shlCl true 0x0 0x41 == some (0x0, some false, some true, some false, some false)
#guard shlCl true 0x0 0x100 == some (0x0, some true, some true, some true, some true)
#guard shlCl false 0x0 0x100 == some (0x0, some false, some false, some false, some false)
#guard shlCl true 0x0 0x13f == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x0 0xffffffffffffff21 == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x1 0x1 == some (0x2, some false, some false, some false, some false)
#guard shlCl false 0x1 0x1 == some (0x2, some false, some false, some false, some false)
#guard shlCl true 0x1 0x3f == some (0x8000000000000000, some false, some false, some true, none)
#guard shlCl true 0x8000000000000000 0x0 == some (0x8000000000000000, some true, some true, some true, some true)
#guard shlCl false 0x8000000000000000 0x0 == some (0x8000000000000000, some false, some false, some false, some false)
#guard shlCl true 0x8000000000000000 0x1 == some (0x0, some true, some true, some false, some true)
#guard shlCl false 0x8000000000000000 0x1 == some (0x0, some true, some true, some false, some true)
#guard shlCl true 0x8000000000000000 0x4 == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x8000000000000000 0x3f == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x8000000000000000 0x40 == some (0x8000000000000000, some true, some true, some true, some true)
#guard shlCl false 0x8000000000000000 0x40 == some (0x8000000000000000, some false, some false, some false, some false)
#guard shlCl true 0x8000000000000000 0x41 == some (0x0, some true, some true, some false, some true)
#guard shlCl true 0x8000000000000000 0x100 == some (0x8000000000000000, some true, some true, some true, some true)
#guard shlCl false 0x8000000000000000 0x100 == some (0x8000000000000000, some false, some false, some false, some false)
#guard shlCl true 0x8000000000000000 0x13f == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x8000000000000000 0xffffffffffffff21 == some (0x0, some false, some true, some false, none)
#guard shlCl true 0xffffffffffffffff 0x0 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard shlCl false 0xffffffffffffffff 0x0 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard shlCl true 0xffffffffffffffff 0x1 == some (0xfffffffffffffffe, some true, some false, some true, some false)
#guard shlCl false 0xffffffffffffffff 0x1 == some (0xfffffffffffffffe, some true, some false, some true, some false)
#guard shlCl true 0xffffffffffffffff 0x4 == some (0xfffffffffffffff0, some true, some false, some true, none)
#guard shlCl true 0xffffffffffffffff 0x3f == some (0x8000000000000000, some true, some false, some true, none)
#guard shlCl true 0xffffffffffffffff 0x40 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard shlCl false 0xffffffffffffffff 0x40 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard shlCl true 0xffffffffffffffff 0x41 == some (0xfffffffffffffffe, some true, some false, some true, some false)
#guard shlCl true 0xffffffffffffffff 0x100 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard shlCl false 0xffffffffffffffff 0x100 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard shlCl true 0xffffffffffffffff 0x13f == some (0x8000000000000000, some true, some false, some true, none)
#guard shlCl true 0xffffffffffffffff 0xffffffffffffff21 == some (0xfffffffe00000000, some true, some false, some true, none)
#guard shlCl true 0xdeadbeef80000001 0x0 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard shlCl false 0xdeadbeef80000001 0x0 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard shlCl true 0xdeadbeef80000001 0x1 == some (0xbd5b7ddf00000002, some true, some false, some true, some false)
#guard shlCl false 0xdeadbeef80000001 0x1 == some (0xbd5b7ddf00000002, some true, some false, some true, some false)
#guard shlCl true 0xdeadbeef80000001 0x4 == some (0xeadbeef800000010, some true, some false, some true, none)
#guard shlCl true 0xdeadbeef80000001 0x3f == some (0x8000000000000000, some false, some false, some true, none)
#guard shlCl true 0xdeadbeef80000001 0x40 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard shlCl false 0xdeadbeef80000001 0x40 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard shlCl true 0xdeadbeef80000001 0x41 == some (0xbd5b7ddf00000002, some true, some false, some true, some false)
#guard shlCl true 0xdeadbeef80000001 0x100 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard shlCl false 0xdeadbeef80000001 0x100 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard shlCl true 0xdeadbeef80000001 0x13f == some (0x8000000000000000, some false, some false, some true, none)
#guard shlCl true 0xdeadbeef80000001 0xffffffffffffff21 == some (0x200000000, some true, some false, some false, none)
#guard shlCl true 0x6a09e667f3bcc908 0x0 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard shlCl false 0x6a09e667f3bcc908 0x0 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard shlCl true 0x6a09e667f3bcc908 0x1 == some (0xd413cccfe7799210, some false, some false, some true, some true)
#guard shlCl false 0x6a09e667f3bcc908 0x1 == some (0xd413cccfe7799210, some false, some false, some true, some true)
#guard shlCl true 0x6a09e667f3bcc908 0x4 == some (0xa09e667f3bcc9080, some false, some false, some true, none)
#guard shlCl true 0x6a09e667f3bcc908 0x3f == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x6a09e667f3bcc908 0x40 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard shlCl false 0x6a09e667f3bcc908 0x40 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard shlCl true 0x6a09e667f3bcc908 0x41 == some (0xd413cccfe7799210, some false, some false, some true, some true)
#guard shlCl true 0x6a09e667f3bcc908 0x100 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard shlCl false 0x6a09e667f3bcc908 0x100 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard shlCl true 0x6a09e667f3bcc908 0x13f == some (0x0, some false, some true, some false, none)
#guard shlCl true 0x6a09e667f3bcc908 0xffffffffffffff21 == some (0xe779921000000000, some true, some false, some true, none)
#guard shlCl true 0x4000000000000000 0x1 == some (0x8000000000000000, some false, some false, some true, some true)
#guard shlCl false 0x4000000000000000 0x1 == some (0x8000000000000000, some false, some false, some true, some true)
#guard shlCl true 0x4000000000000000 0x3f == some (0x0, some false, some true, some false, none)
#guard shrCl true 0x0 0x0 == some (0x0, some true, some true, some true, some true)
#guard shrCl false 0x0 0x0 == some (0x0, some false, some false, some false, some false)
#guard shrCl true 0x0 0x1 == some (0x0, some false, some true, some false, some false)
#guard shrCl false 0x0 0x1 == some (0x0, some false, some true, some false, some false)
#guard shrCl true 0x0 0x4 == some (0x0, some false, some true, some false, none)
#guard shrCl true 0x0 0x3f == some (0x0, some false, some true, some false, none)
#guard shrCl true 0x0 0x40 == some (0x0, some true, some true, some true, some true)
#guard shrCl false 0x0 0x40 == some (0x0, some false, some false, some false, some false)
#guard shrCl true 0x0 0x41 == some (0x0, some false, some true, some false, some false)
#guard shrCl true 0x0 0x100 == some (0x0, some true, some true, some true, some true)
#guard shrCl false 0x0 0x100 == some (0x0, some false, some false, some false, some false)
#guard shrCl true 0x0 0x13f == some (0x0, some false, some true, some false, none)
#guard shrCl true 0x0 0xffffffffffffff21 == some (0x0, some false, some true, some false, none)
#guard shrCl true 0x1 0x1 == some (0x0, some true, some true, some false, some false)
#guard shrCl false 0x1 0x1 == some (0x0, some true, some true, some false, some false)
#guard shrCl true 0x1 0x3f == some (0x0, some false, some true, some false, none)
#guard shrCl true 0x8000000000000000 0x0 == some (0x8000000000000000, some true, some true, some true, some true)
#guard shrCl false 0x8000000000000000 0x0 == some (0x8000000000000000, some false, some false, some false, some false)
#guard shrCl true 0x8000000000000000 0x1 == some (0x4000000000000000, some false, some false, some false, some true)
#guard shrCl false 0x8000000000000000 0x1 == some (0x4000000000000000, some false, some false, some false, some true)
#guard shrCl true 0x8000000000000000 0x4 == some (0x800000000000000, some false, some false, some false, none)
#guard shrCl true 0x8000000000000000 0x3f == some (0x1, some false, some false, some false, none)
#guard shrCl true 0x8000000000000000 0x40 == some (0x8000000000000000, some true, some true, some true, some true)
#guard shrCl false 0x8000000000000000 0x40 == some (0x8000000000000000, some false, some false, some false, some false)
#guard shrCl true 0x8000000000000000 0x41 == some (0x4000000000000000, some false, some false, some false, some true)
#guard shrCl true 0x8000000000000000 0x100 == some (0x8000000000000000, some true, some true, some true, some true)
#guard shrCl false 0x8000000000000000 0x100 == some (0x8000000000000000, some false, some false, some false, some false)
#guard shrCl true 0x8000000000000000 0x13f == some (0x1, some false, some false, some false, none)
#guard shrCl true 0x8000000000000000 0xffffffffffffff21 == some (0x40000000, some false, some false, some false, none)
#guard shrCl true 0xffffffffffffffff 0x0 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard shrCl false 0xffffffffffffffff 0x0 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard shrCl true 0xffffffffffffffff 0x1 == some (0x7fffffffffffffff, some true, some false, some false, some true)
#guard shrCl false 0xffffffffffffffff 0x1 == some (0x7fffffffffffffff, some true, some false, some false, some true)
#guard shrCl true 0xffffffffffffffff 0x4 == some (0xfffffffffffffff, some true, some false, some false, none)
#guard shrCl true 0xffffffffffffffff 0x3f == some (0x1, some true, some false, some false, none)
#guard shrCl true 0xffffffffffffffff 0x40 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard shrCl false 0xffffffffffffffff 0x40 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard shrCl true 0xffffffffffffffff 0x41 == some (0x7fffffffffffffff, some true, some false, some false, some true)
#guard shrCl true 0xffffffffffffffff 0x100 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard shrCl false 0xffffffffffffffff 0x100 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard shrCl true 0xffffffffffffffff 0x13f == some (0x1, some true, some false, some false, none)
#guard shrCl true 0xffffffffffffffff 0xffffffffffffff21 == some (0x7fffffff, some true, some false, some false, none)
#guard shrCl true 0xdeadbeef80000001 0x0 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard shrCl false 0xdeadbeef80000001 0x0 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard shrCl true 0xdeadbeef80000001 0x1 == some (0x6f56df77c0000000, some true, some false, some false, some true)
#guard shrCl false 0xdeadbeef80000001 0x1 == some (0x6f56df77c0000000, some true, some false, some false, some true)
#guard shrCl true 0xdeadbeef80000001 0x4 == some (0xdeadbeef8000000, some false, some false, some false, none)
#guard shrCl true 0xdeadbeef80000001 0x3f == some (0x1, some true, some false, some false, none)
#guard shrCl true 0xdeadbeef80000001 0x40 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard shrCl false 0xdeadbeef80000001 0x40 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard shrCl true 0xdeadbeef80000001 0x41 == some (0x6f56df77c0000000, some true, some false, some false, some true)
#guard shrCl true 0xdeadbeef80000001 0x100 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard shrCl false 0xdeadbeef80000001 0x100 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard shrCl true 0xdeadbeef80000001 0x13f == some (0x1, some true, some false, some false, none)
#guard shrCl true 0xdeadbeef80000001 0xffffffffffffff21 == some (0x6f56df77, some true, some false, some false, none)
#guard shrCl true 0x6a09e667f3bcc908 0x0 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard shrCl false 0x6a09e667f3bcc908 0x0 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard shrCl true 0x6a09e667f3bcc908 0x1 == some (0x3504f333f9de6484, some false, some false, some false, some false)
#guard shrCl false 0x6a09e667f3bcc908 0x1 == some (0x3504f333f9de6484, some false, some false, some false, some false)
#guard shrCl true 0x6a09e667f3bcc908 0x4 == some (0x6a09e667f3bcc90, some true, some false, some false, none)
#guard shrCl true 0x6a09e667f3bcc908 0x3f == some (0x0, some true, some true, some false, none)
#guard shrCl true 0x6a09e667f3bcc908 0x40 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard shrCl false 0x6a09e667f3bcc908 0x40 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard shrCl true 0x6a09e667f3bcc908 0x41 == some (0x3504f333f9de6484, some false, some false, some false, some false)
#guard shrCl true 0x6a09e667f3bcc908 0x100 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard shrCl false 0x6a09e667f3bcc908 0x100 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard shrCl true 0x6a09e667f3bcc908 0x13f == some (0x0, some true, some true, some false, none)
#guard shrCl true 0x6a09e667f3bcc908 0xffffffffffffff21 == some (0x3504f333, some true, some false, some false, none)
#guard shrCl true 0x4000000000000000 0x1 == some (0x2000000000000000, some false, some false, some false, some false)
#guard shrCl false 0x4000000000000000 0x1 == some (0x2000000000000000, some false, some false, some false, some false)
#guard shrCl true 0x4000000000000000 0x3f == some (0x0, some true, some true, some false, none)
#guard sarCl true 0x0 0x0 == some (0x0, some true, some true, some true, some true)
#guard sarCl false 0x0 0x0 == some (0x0, some false, some false, some false, some false)
#guard sarCl true 0x0 0x1 == some (0x0, some false, some true, some false, some false)
#guard sarCl false 0x0 0x1 == some (0x0, some false, some true, some false, some false)
#guard sarCl true 0x0 0x4 == some (0x0, some false, some true, some false, none)
#guard sarCl true 0x0 0x3f == some (0x0, some false, some true, some false, none)
#guard sarCl true 0x0 0x40 == some (0x0, some true, some true, some true, some true)
#guard sarCl false 0x0 0x40 == some (0x0, some false, some false, some false, some false)
#guard sarCl true 0x0 0x41 == some (0x0, some false, some true, some false, some false)
#guard sarCl true 0x0 0x100 == some (0x0, some true, some true, some true, some true)
#guard sarCl false 0x0 0x100 == some (0x0, some false, some false, some false, some false)
#guard sarCl true 0x0 0x13f == some (0x0, some false, some true, some false, none)
#guard sarCl true 0x0 0xffffffffffffff21 == some (0x0, some false, some true, some false, none)
#guard sarCl true 0x1 0x1 == some (0x0, some true, some true, some false, some false)
#guard sarCl false 0x1 0x1 == some (0x0, some true, some true, some false, some false)
#guard sarCl true 0x1 0x3f == some (0x0, some false, some true, some false, none)
#guard sarCl true 0x8000000000000000 0x0 == some (0x8000000000000000, some true, some true, some true, some true)
#guard sarCl false 0x8000000000000000 0x0 == some (0x8000000000000000, some false, some false, some false, some false)
#guard sarCl true 0x8000000000000000 0x1 == some (0xc000000000000000, some false, some false, some true, some false)
#guard sarCl false 0x8000000000000000 0x1 == some (0xc000000000000000, some false, some false, some true, some false)
#guard sarCl true 0x8000000000000000 0x4 == some (0xf800000000000000, some false, some false, some true, none)
#guard sarCl true 0x8000000000000000 0x3f == some (0xffffffffffffffff, some false, some false, some true, none)
#guard sarCl true 0x8000000000000000 0x40 == some (0x8000000000000000, some true, some true, some true, some true)
#guard sarCl false 0x8000000000000000 0x40 == some (0x8000000000000000, some false, some false, some false, some false)
#guard sarCl true 0x8000000000000000 0x41 == some (0xc000000000000000, some false, some false, some true, some false)
#guard sarCl true 0x8000000000000000 0x100 == some (0x8000000000000000, some true, some true, some true, some true)
#guard sarCl false 0x8000000000000000 0x100 == some (0x8000000000000000, some false, some false, some false, some false)
#guard sarCl true 0x8000000000000000 0x13f == some (0xffffffffffffffff, some false, some false, some true, none)
#guard sarCl true 0x8000000000000000 0xffffffffffffff21 == some (0xffffffffc0000000, some false, some false, some true, none)
#guard sarCl true 0xffffffffffffffff 0x0 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard sarCl false 0xffffffffffffffff 0x0 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard sarCl true 0xffffffffffffffff 0x1 == some (0xffffffffffffffff, some true, some false, some true, some false)
#guard sarCl false 0xffffffffffffffff 0x1 == some (0xffffffffffffffff, some true, some false, some true, some false)
#guard sarCl true 0xffffffffffffffff 0x4 == some (0xffffffffffffffff, some true, some false, some true, none)
#guard sarCl true 0xffffffffffffffff 0x3f == some (0xffffffffffffffff, some true, some false, some true, none)
#guard sarCl true 0xffffffffffffffff 0x40 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard sarCl false 0xffffffffffffffff 0x40 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard sarCl true 0xffffffffffffffff 0x41 == some (0xffffffffffffffff, some true, some false, some true, some false)
#guard sarCl true 0xffffffffffffffff 0x100 == some (0xffffffffffffffff, some true, some true, some true, some true)
#guard sarCl false 0xffffffffffffffff 0x100 == some (0xffffffffffffffff, some false, some false, some false, some false)
#guard sarCl true 0xffffffffffffffff 0x13f == some (0xffffffffffffffff, some true, some false, some true, none)
#guard sarCl true 0xffffffffffffffff 0xffffffffffffff21 == some (0xffffffffffffffff, some true, some false, some true, none)
#guard sarCl true 0xdeadbeef80000001 0x0 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard sarCl false 0xdeadbeef80000001 0x0 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard sarCl true 0xdeadbeef80000001 0x1 == some (0xef56df77c0000000, some true, some false, some true, some false)
#guard sarCl false 0xdeadbeef80000001 0x1 == some (0xef56df77c0000000, some true, some false, some true, some false)
#guard sarCl true 0xdeadbeef80000001 0x4 == some (0xfdeadbeef8000000, some false, some false, some true, none)
#guard sarCl true 0xdeadbeef80000001 0x3f == some (0xffffffffffffffff, some true, some false, some true, none)
#guard sarCl true 0xdeadbeef80000001 0x40 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard sarCl false 0xdeadbeef80000001 0x40 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard sarCl true 0xdeadbeef80000001 0x41 == some (0xef56df77c0000000, some true, some false, some true, some false)
#guard sarCl true 0xdeadbeef80000001 0x100 == some (0xdeadbeef80000001, some true, some true, some true, some true)
#guard sarCl false 0xdeadbeef80000001 0x100 == some (0xdeadbeef80000001, some false, some false, some false, some false)
#guard sarCl true 0xdeadbeef80000001 0x13f == some (0xffffffffffffffff, some true, some false, some true, none)
#guard sarCl true 0xdeadbeef80000001 0xffffffffffffff21 == some (0xffffffffef56df77, some true, some false, some true, none)
#guard sarCl true 0x6a09e667f3bcc908 0x0 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard sarCl false 0x6a09e667f3bcc908 0x0 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard sarCl true 0x6a09e667f3bcc908 0x1 == some (0x3504f333f9de6484, some false, some false, some false, some false)
#guard sarCl false 0x6a09e667f3bcc908 0x1 == some (0x3504f333f9de6484, some false, some false, some false, some false)
#guard sarCl true 0x6a09e667f3bcc908 0x4 == some (0x6a09e667f3bcc90, some true, some false, some false, none)
#guard sarCl true 0x6a09e667f3bcc908 0x3f == some (0x0, some true, some true, some false, none)
#guard sarCl true 0x6a09e667f3bcc908 0x40 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard sarCl false 0x6a09e667f3bcc908 0x40 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard sarCl true 0x6a09e667f3bcc908 0x41 == some (0x3504f333f9de6484, some false, some false, some false, some false)
#guard sarCl true 0x6a09e667f3bcc908 0x100 == some (0x6a09e667f3bcc908, some true, some true, some true, some true)
#guard sarCl false 0x6a09e667f3bcc908 0x100 == some (0x6a09e667f3bcc908, some false, some false, some false, some false)
#guard sarCl true 0x6a09e667f3bcc908 0x13f == some (0x0, some true, some true, some false, none)
#guard sarCl true 0x6a09e667f3bcc908 0xffffffffffffff21 == some (0x3504f333, some true, some false, some false, none)
#guard sarCl true 0x4000000000000000 0x1 == some (0x2000000000000000, some false, some false, some false, some false)
#guard sarCl false 0x4000000000000000 0x1 == some (0x2000000000000000, some false, some false, some false, some false)
#guard sarCl true 0x4000000000000000 0x3f == some (0x0, some true, some true, some false, none)

-- The other registers do not change, and `rcx` may be the destination:
-- `sar rcx, cl` shifts by the count it held (on the CPU, with every flag
-- clear before: `0x0123456789abcd05` gives `0x91a2b3c4d5e68`, CF, ZF, SF
-- and OF clear; `0x8000000000000041` gives `0xc000000000000020`, CF and SF
-- set; `0xffffffffffffff3f` gives `0xffffffffffffffff`, CF and SF set).
#guard (exec (.shiftCl .shl .rdx) (s true 3 5)).map (fun t => (t.gpr .rcx, t.gpr .r8, t.gpr .rax)) ==
  some (5, 3, 0xcccccccccccccccc)
#guard (exec (.shiftCl .sar .rcx) (s false 0 0x0123456789abcd05)).map
  (fun t => (t.gpr .rcx, t.cf, t.zf, t.sf, t.of)) ==
  some (0x91a2b3c4d5e68, some false, some false, some false, none)
#guard (exec (.shiftCl .sar .rcx) (s false 0 0x8000000000000041)).map
  (fun t => (t.gpr .rcx, t.cf, t.zf, t.sf, t.of)) ==
  some (0xc000000000000020, some true, some false, some true, some false)
#guard (exec (.shiftCl .sar .rcx) (s false 0 0xffffffffffffff3f)).map
  (fun t => (t.gpr .rcx, t.cf, t.zf, t.sf, t.of)) ==
  some (0xffffffffffffffff, some true, some false, some true, none)

/-! ## `shlx` and `shrx` -/

/-- Whether `op rdx, r8, rcx`, with `a` in `r8` and `c` in `rcx` and CF and
SF set and ZF and OF clear, leaves `r` in `rdx` and the flags unchanged. -/
def x (op : ShiftxOp) (a c r : BitVec 64) : Bool :=
  (exec (.shiftx op .rdx .r8 .rcx) { s false a c with cf := some true, sf := some true }).map
    (fun t => (t.gpr .rdx, t.cf, t.zf, t.sf, t.of)) ==
    some (r, some true, some false, some true, some false)

def shlx := x .shlx
def shrx := x .shrx

#guard shlx 0x0 0x0 0x0
#guard shlx 0x0 0x1 0x0
#guard shlx 0x0 0x4 0x0
#guard shlx 0x0 0x3f 0x0
#guard shlx 0x0 0x40 0x0
#guard shlx 0x0 0x41 0x0
#guard shlx 0x0 0x100 0x0
#guard shlx 0x0 0x13f 0x0
#guard shlx 0x0 0xffffffffffffff21 0x0
#guard shlx 0x1 0x0 0x1
#guard shlx 0x1 0x1 0x2
#guard shlx 0x1 0x4 0x10
#guard shlx 0x1 0x3f 0x8000000000000000
#guard shlx 0x1 0x40 0x1
#guard shlx 0x1 0x41 0x2
#guard shlx 0x1 0x100 0x1
#guard shlx 0x1 0x13f 0x8000000000000000
#guard shlx 0x1 0xffffffffffffff21 0x200000000
#guard shlx 0x8000000000000000 0x0 0x8000000000000000
#guard shlx 0x8000000000000000 0x1 0x0
#guard shlx 0x8000000000000000 0x4 0x0
#guard shlx 0x8000000000000000 0x3f 0x0
#guard shlx 0x8000000000000000 0x40 0x8000000000000000
#guard shlx 0x8000000000000000 0x41 0x0
#guard shlx 0x8000000000000000 0x100 0x8000000000000000
#guard shlx 0x8000000000000000 0x13f 0x0
#guard shlx 0x8000000000000000 0xffffffffffffff21 0x0
#guard shlx 0xffffffffffffffff 0x0 0xffffffffffffffff
#guard shlx 0xffffffffffffffff 0x1 0xfffffffffffffffe
#guard shlx 0xffffffffffffffff 0x4 0xfffffffffffffff0
#guard shlx 0xffffffffffffffff 0x3f 0x8000000000000000
#guard shlx 0xffffffffffffffff 0x40 0xffffffffffffffff
#guard shlx 0xffffffffffffffff 0x41 0xfffffffffffffffe
#guard shlx 0xffffffffffffffff 0x100 0xffffffffffffffff
#guard shlx 0xffffffffffffffff 0x13f 0x8000000000000000
#guard shlx 0xffffffffffffffff 0xffffffffffffff21 0xfffffffe00000000
#guard shlx 0xdeadbeef80000001 0x0 0xdeadbeef80000001
#guard shlx 0xdeadbeef80000001 0x1 0xbd5b7ddf00000002
#guard shlx 0xdeadbeef80000001 0x4 0xeadbeef800000010
#guard shlx 0xdeadbeef80000001 0x3f 0x8000000000000000
#guard shlx 0xdeadbeef80000001 0x40 0xdeadbeef80000001
#guard shlx 0xdeadbeef80000001 0x41 0xbd5b7ddf00000002
#guard shlx 0xdeadbeef80000001 0x100 0xdeadbeef80000001
#guard shlx 0xdeadbeef80000001 0x13f 0x8000000000000000
#guard shlx 0xdeadbeef80000001 0xffffffffffffff21 0x200000000
#guard shlx 0x6a09e667f3bcc908 0x0 0x6a09e667f3bcc908
#guard shlx 0x6a09e667f3bcc908 0x1 0xd413cccfe7799210
#guard shlx 0x6a09e667f3bcc908 0x4 0xa09e667f3bcc9080
#guard shlx 0x6a09e667f3bcc908 0x3f 0x0
#guard shlx 0x6a09e667f3bcc908 0x40 0x6a09e667f3bcc908
#guard shlx 0x6a09e667f3bcc908 0x41 0xd413cccfe7799210
#guard shlx 0x6a09e667f3bcc908 0x100 0x6a09e667f3bcc908
#guard shlx 0x6a09e667f3bcc908 0x13f 0x0
#guard shlx 0x6a09e667f3bcc908 0xffffffffffffff21 0xe779921000000000
#guard shrx 0x0 0x0 0x0
#guard shrx 0x0 0x1 0x0
#guard shrx 0x0 0x4 0x0
#guard shrx 0x0 0x3f 0x0
#guard shrx 0x0 0x40 0x0
#guard shrx 0x0 0x41 0x0
#guard shrx 0x0 0x100 0x0
#guard shrx 0x0 0x13f 0x0
#guard shrx 0x0 0xffffffffffffff21 0x0
#guard shrx 0x1 0x0 0x1
#guard shrx 0x1 0x1 0x0
#guard shrx 0x1 0x4 0x0
#guard shrx 0x1 0x3f 0x0
#guard shrx 0x1 0x40 0x1
#guard shrx 0x1 0x41 0x0
#guard shrx 0x1 0x100 0x1
#guard shrx 0x1 0x13f 0x0
#guard shrx 0x1 0xffffffffffffff21 0x0
#guard shrx 0x8000000000000000 0x0 0x8000000000000000
#guard shrx 0x8000000000000000 0x1 0x4000000000000000
#guard shrx 0x8000000000000000 0x4 0x800000000000000
#guard shrx 0x8000000000000000 0x3f 0x1
#guard shrx 0x8000000000000000 0x40 0x8000000000000000
#guard shrx 0x8000000000000000 0x41 0x4000000000000000
#guard shrx 0x8000000000000000 0x100 0x8000000000000000
#guard shrx 0x8000000000000000 0x13f 0x1
#guard shrx 0x8000000000000000 0xffffffffffffff21 0x40000000
#guard shrx 0xffffffffffffffff 0x0 0xffffffffffffffff
#guard shrx 0xffffffffffffffff 0x1 0x7fffffffffffffff
#guard shrx 0xffffffffffffffff 0x4 0xfffffffffffffff
#guard shrx 0xffffffffffffffff 0x3f 0x1
#guard shrx 0xffffffffffffffff 0x40 0xffffffffffffffff
#guard shrx 0xffffffffffffffff 0x41 0x7fffffffffffffff
#guard shrx 0xffffffffffffffff 0x100 0xffffffffffffffff
#guard shrx 0xffffffffffffffff 0x13f 0x1
#guard shrx 0xffffffffffffffff 0xffffffffffffff21 0x7fffffff
#guard shrx 0xdeadbeef80000001 0x0 0xdeadbeef80000001
#guard shrx 0xdeadbeef80000001 0x1 0x6f56df77c0000000
#guard shrx 0xdeadbeef80000001 0x4 0xdeadbeef8000000
#guard shrx 0xdeadbeef80000001 0x3f 0x1
#guard shrx 0xdeadbeef80000001 0x40 0xdeadbeef80000001
#guard shrx 0xdeadbeef80000001 0x41 0x6f56df77c0000000
#guard shrx 0xdeadbeef80000001 0x100 0xdeadbeef80000001
#guard shrx 0xdeadbeef80000001 0x13f 0x1
#guard shrx 0xdeadbeef80000001 0xffffffffffffff21 0x6f56df77
#guard shrx 0x6a09e667f3bcc908 0x0 0x6a09e667f3bcc908
#guard shrx 0x6a09e667f3bcc908 0x1 0x3504f333f9de6484
#guard shrx 0x6a09e667f3bcc908 0x4 0x6a09e667f3bcc90
#guard shrx 0x6a09e667f3bcc908 0x3f 0x0
#guard shrx 0x6a09e667f3bcc908 0x40 0x6a09e667f3bcc908
#guard shrx 0x6a09e667f3bcc908 0x41 0x3504f333f9de6484
#guard shrx 0x6a09e667f3bcc908 0x100 0x6a09e667f3bcc908
#guard shrx 0x6a09e667f3bcc908 0x13f 0x0
#guard shrx 0x6a09e667f3bcc908 0xffffffffffffff21 0x3504f333

-- Only the destination changes; `rcx` may be the destination.
#guard (exec (.shiftx .shlx .rdx .r8 .rcx) (s true 3 5)).map
  (fun t => (t.gpr .r8, t.gpr .rcx, t.gpr .rax)) == some (3, 5, 0xcccccccccccccccc)
#guard (exec (.shiftx .shrx .rcx .r8 .rcx) (s true 0x100 4)).map (fun t => t.gpr .rcx) == some 0x10

/-! ## Printing -/

#guard Instr.asm (.shiftCl .shl .rdx) == ["shl rdx, cl"]
#guard Instr.asm (.shiftCl .shr .r8) == ["shr r8, cl"]
#guard Instr.asm (.shiftCl .sar .rax) == ["sar rax, cl"]
#guard Instr.asm (.shiftx .shlx .rax .rbx .rcx) == ["shlx rax, rbx, rcx"]
#guard Instr.asm (.shiftx .shrx .r8 .r15 .rdx) == ["shrx r8, r15, rdx"]

-- Their CPU features (the SDM's "CPUID Feature Flag": BMI2 for `shlx` and
-- `shrx`, none for the shifts by CL); none writes `rsp` unless it is the
-- destination.
#guard isa.requires (.shiftCl .shl .rax) == []
#guard isa.requires (.shiftx .shlx .rax .rbx .rcx) == ["bmi2"]
#guard isa.requires (.shiftx .shrx .rax .rbx .rcx) == ["bmi2"]
#guard !isa.writesSp (.shiftCl .shl .rax)
#guard isa.writesSp (.shiftCl .sar .rsp)
#guard !isa.writesSp (.shiftx .shlx .rax .rsp .rsp)
#guard isa.writesSp (.shiftx .shrx .rsp .rax .rbx)

end VG.Test.X86_64VarShift
