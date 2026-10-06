import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `shl` and `cmovcc`

Each expected value was computed on an x86-64 CPU (an Intel Xeon), by the
same instruction in inline assembly, with RFLAGS set by `popfq` before it
and read by `pushfq` after it, and is compared with the model's result on
the same inputs: `shl r64, imm8` by 1, 4, 32 and 63 and `shl r32, imm8` by
1, 8 and 31 (into a register whose upper half is not zero), with every flag
preset, so that each one the instruction writes is seen to change; and
`cmovb`, `cmovae`, `cmove` and `cmovne` from a register and from memory,
with each combination of CF and ZF (SF set and OF clear, which they keep).
OF after a shift by more than 1 is undefined in the model (`none`), and is
not compared. This tests the transcription of the SDM's pseudocode (which
bit is the last shifted out, how OF is computed, which flag each condition
reads and whether it moves when it holds), which review of the TCB would
otherwise have to catch by eye. On the same CPU, `cmovb` with CF clear (not
moving) from an unmapped address faults, as the model's does from outside
the readable regions.
-/

namespace VG.Test.X86_64ShlCmov

open X86_64

/-- A state with `a` in `rcx`, `0x1111111111111111` in `r8`, `0x1000` in
`rsi`, `0xcccccccccccccccc` in every other register, the given flags, and
the 8 bytes at `0x1000`, `0xfedcba9876543210` (little-endian), readable. -/
def s (a : BitVec 64) (cf zf sf of : Bool) : State where
  gpr r := if r = .rcx then a else if r = .r8 then 0x1111111111111111 else if r = .rsi then 0x1000
    else 0xcccccccccccccccc
  cf := some cf
  zf := some zf
  sf := some sf
  of := some of
  mem addr := if 0x1000 ≤ addr.toNat ∧ addr.toNat < 0x1008 then
    (0xfedcba9876543210 : BitVec 64).extractLsb' (8 * (addr.toNat - 0x1000)) 8 else 0
  rd := [⟨0x1000, 8⟩]
  wr := []

#guard (s 0 false false false false).load64 0x1000 == some 0xfedcba9876543210

/-! ## `shl` -/

/-- `rcx` and CF, ZF, SF and OF after `shl rcx, n` with `a` in `rcx` and
every flag set before. -/
def shl (n : Nat) (a : BitVec 64) :
    Option (BitVec 64 × Option Bool × Option Bool × Option Bool × Option Bool) :=
  (exec (.shift .shl .rcx n) (s a true true true true)).map
    fun t => (t.gpr .rcx, t.cf, t.zf, t.sf, t.of)

#guard shl 1 0x0 == some (0x0, some false, some true, some false, some false)
#guard shl 4 0x0 == some (0x0, some false, some true, some false, none)
#guard shl 32 0x0 == some (0x0, some false, some true, some false, none)
#guard shl 63 0x0 == some (0x0, some false, some true, some false, none)
#guard shl 1 0x1 == some (0x2, some false, some false, some false, some false)
#guard shl 4 0x1 == some (0x10, some false, some false, some false, none)
#guard shl 32 0x1 == some (0x100000000, some false, some false, some false, none)
#guard shl 63 0x1 == some (0x8000000000000000, some false, some false, some true, none)
#guard shl 1 0x3 == some (0x6, some false, some false, some false, some false)
#guard shl 4 0x3 == some (0x30, some false, some false, some false, none)
#guard shl 32 0x3 == some (0x300000000, some false, some false, some false, none)
#guard shl 63 0x3 == some (0x8000000000000000, some true, some false, some true, none)
#guard shl 1 0x8000000000000000 == some (0x0, some true, some true, some false, some true)
#guard shl 4 0x8000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 32 0x8000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 63 0x8000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 1 0x4000000000000000 == some (0x8000000000000000, some false, some false, some true, some true)
#guard shl 4 0x4000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 32 0x4000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 63 0x4000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 1 0xc000000000000000 == some (0x8000000000000000, some true, some false, some true, some false)
#guard shl 4 0xc000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 32 0xc000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 63 0xc000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl 1 0x7fffffffffffffff == some (0xfffffffffffffffe, some false, some false, some true, some true)
#guard shl 4 0x7fffffffffffffff == some (0xfffffffffffffff0, some true, some false, some true, none)
#guard shl 32 0x7fffffffffffffff == some (0xffffffff00000000, some true, some false, some true, none)
#guard shl 63 0x7fffffffffffffff == some (0x8000000000000000, some true, some false, some true, none)
#guard shl 1 0xffffffffffffffff == some (0xfffffffffffffffe, some true, some false, some true, some false)
#guard shl 4 0xffffffffffffffff == some (0xfffffffffffffff0, some true, some false, some true, none)
#guard shl 32 0xffffffffffffffff == some (0xffffffff00000000, some true, some false, some true, none)
#guard shl 63 0xffffffffffffffff == some (0x8000000000000000, some true, some false, some true, none)
#guard shl 1 0x123456789abcdef0 == some (0x2468acf13579bde0, some false, some false, some false, some false)
#guard shl 4 0x123456789abcdef0 == some (0x23456789abcdef00, some true, some false, some false, none)
#guard shl 32 0x123456789abcdef0 == some (0x9abcdef000000000, some false, some false, some true, none)
#guard shl 63 0x123456789abcdef0 == some (0x0, some false, some true, some false, none)
#guard shl 1 0xfedcba9876543210 == some (0xfdb97530eca86420, some true, some false, some true, some false)
#guard shl 4 0xfedcba9876543210 == some (0xedcba98765432100, some true, some false, some true, none)
#guard shl 32 0xfedcba9876543210 == some (0x7654321000000000, some false, some false, some false, none)
#guard shl 63 0xfedcba9876543210 == some (0x0, some false, some true, some false, none)
#guard shl 1 0xdeadbeef80000000 == some (0xbd5b7ddf00000000, some true, some false, some true, some false)
#guard shl 4 0xdeadbeef80000000 == some (0xeadbeef800000000, some true, some false, some true, none)
#guard shl 32 0xdeadbeef80000000 == some (0x8000000000000000, some true, some false, some true, none)
#guard shl 63 0xdeadbeef80000000 == some (0x0, some false, some true, some false, none)
#guard shl 1 0xc0000001 == some (0x180000002, some false, some false, some false, some false)
#guard shl 4 0xc0000001 == some (0xc00000010, some false, some false, some false, none)
#guard shl 32 0xc0000001 == some (0xc000000100000000, some false, some false, some true, none)
#guard shl 63 0xc0000001 == some (0x8000000000000000, some false, some false, some true, none)

/-- `rcx` and CF, ZF, SF and OF after `shl ecx, n` with `a` in `rcx` and
every flag set before: the 32-bit result, zero-extended. -/
def shl32 (n : Nat) (a : BitVec 64) :
    Option (BitVec 64 × Option Bool × Option Bool × Option Bool × Option Bool) :=
  (exec (.shift32 .shl .rcx n) (s a true true true true)).map
    fun t => (t.gpr .rcx, t.cf, t.zf, t.sf, t.of)

#guard shl32 1 0x0 == some (0x0, some false, some true, some false, some false)
#guard shl32 8 0x0 == some (0x0, some false, some true, some false, none)
#guard shl32 31 0x0 == some (0x0, some false, some true, some false, none)
#guard shl32 1 0x1 == some (0x2, some false, some false, some false, some false)
#guard shl32 8 0x1 == some (0x100, some false, some false, some false, none)
#guard shl32 31 0x1 == some (0x80000000, some false, some false, some true, none)
#guard shl32 1 0x3 == some (0x6, some false, some false, some false, some false)
#guard shl32 8 0x3 == some (0x300, some false, some false, some false, none)
#guard shl32 31 0x3 == some (0x80000000, some true, some false, some true, none)
#guard shl32 1 0x8000000000000000 == some (0x0, some false, some true, some false, some false)
#guard shl32 8 0x8000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl32 31 0x8000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl32 1 0x4000000000000000 == some (0x0, some false, some true, some false, some false)
#guard shl32 8 0x4000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl32 31 0x4000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl32 1 0xc000000000000000 == some (0x0, some false, some true, some false, some false)
#guard shl32 8 0xc000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl32 31 0xc000000000000000 == some (0x0, some false, some true, some false, none)
#guard shl32 1 0x7fffffffffffffff == some (0xfffffffe, some true, some false, some true, some false)
#guard shl32 8 0x7fffffffffffffff == some (0xffffff00, some true, some false, some true, none)
#guard shl32 31 0x7fffffffffffffff == some (0x80000000, some true, some false, some true, none)
#guard shl32 1 0xffffffffffffffff == some (0xfffffffe, some true, some false, some true, some false)
#guard shl32 8 0xffffffffffffffff == some (0xffffff00, some true, some false, some true, none)
#guard shl32 31 0xffffffffffffffff == some (0x80000000, some true, some false, some true, none)
#guard shl32 1 0x123456789abcdef0 == some (0x3579bde0, some true, some false, some false, some true)
#guard shl32 8 0x123456789abcdef0 == some (0xbcdef000, some false, some false, some true, none)
#guard shl32 31 0x123456789abcdef0 == some (0x0, some false, some true, some false, none)
#guard shl32 1 0xfedcba9876543210 == some (0xeca86420, some false, some false, some true, some true)
#guard shl32 8 0xfedcba9876543210 == some (0x54321000, some false, some false, some false, none)
#guard shl32 31 0xfedcba9876543210 == some (0x0, some false, some true, some false, none)
#guard shl32 1 0xdeadbeef80000000 == some (0x0, some true, some true, some false, some true)
#guard shl32 8 0xdeadbeef80000000 == some (0x0, some false, some true, some false, none)
#guard shl32 31 0xdeadbeef80000000 == some (0x0, some false, some true, some false, none)
#guard shl32 1 0xc0000001 == some (0x80000002, some true, some false, some true, some false)
#guard shl32 8 0xc0000001 == some (0x100, some false, some false, some false, none)
#guard shl32 31 0xc0000001 == some (0x80000000, some false, some false, some true, none)

-- Only the destination changes.
#guard (exec (.shift .shl .rcx 4) (s 3 false false false false)).map
  (fun t => (t.gpr .r8, t.gpr .rsi, t.gpr .rax)) == some (0x1111111111111111, 0x1000, 0xcccccccccccccccc)
#guard (exec (.shift32 .shl .rcx 4) (s 3 false false false false)).map
  (fun t => (t.gpr .r8, t.gpr .rsi, t.gpr .rax)) == some (0x1111111111111111, 0x1000, 0xcccccccccccccccc)
-- Counts outside `1 ≤ n ≤ 63` (`1 ≤ n ≤ 31` for 32 bits) are not modelled: they fault.
#guard (exec (.shift .shl .rcx 0) (s 3 false false false false)).isNone
#guard (exec (.shift .shl .rcx 64) (s 3 false false false false)).isNone
#guard (exec (.shift32 .shl .rcx 0) (s 3 false false false false)).isNone
#guard (exec (.shift32 .shl .rcx 32) (s 3 false false false false)).isNone

/-! ## `cmovcc` -/

/-- `r8` and CF, ZF, SF and OF after `cmovcc r8, src` with
`0x1111111111111111` in `r8`, `0xfedcba9876543210` in `rcx` and at
`[rsi]`, CF and ZF as given, SF set and OF clear. -/
def cmov (cc : Cond) (src : Src) (cf zf : Bool) :
    Option (BitVec 64 × Option Bool × Option Bool × Option Bool × Option Bool) :=
  (exec (.cmov cc .r8 src) (s 0xfedcba9876543210 cf zf true false)).map
    fun t => (t.gpr .r8, t.cf, t.zf, t.sf, t.of)

#guard cmov .b (.reg .rcx) false false == some (0x1111111111111111, some false, some false, some true, some false)
#guard cmov .ae (.reg .rcx) false false == some (0xfedcba9876543210, some false, some false, some true, some false)
#guard cmov .e (.reg .rcx) false false == some (0x1111111111111111, some false, some false, some true, some false)
#guard cmov .ne (.reg .rcx) false false == some (0xfedcba9876543210, some false, some false, some true, some false)
#guard cmov .b (.mem { base := .rsi }) false false == some (0x1111111111111111, some false, some false, some true, some false)
#guard cmov .ae (.mem { base := .rsi }) false false == some (0xfedcba9876543210, some false, some false, some true, some false)
#guard cmov .e (.mem { base := .rsi }) false false == some (0x1111111111111111, some false, some false, some true, some false)
#guard cmov .ne (.mem { base := .rsi }) false false == some (0xfedcba9876543210, some false, some false, some true, some false)
#guard cmov .b (.reg .rcx) false true == some (0x1111111111111111, some false, some true, some true, some false)
#guard cmov .ae (.reg .rcx) false true == some (0xfedcba9876543210, some false, some true, some true, some false)
#guard cmov .e (.reg .rcx) false true == some (0xfedcba9876543210, some false, some true, some true, some false)
#guard cmov .ne (.reg .rcx) false true == some (0x1111111111111111, some false, some true, some true, some false)
#guard cmov .b (.mem { base := .rsi }) false true == some (0x1111111111111111, some false, some true, some true, some false)
#guard cmov .ae (.mem { base := .rsi }) false true == some (0xfedcba9876543210, some false, some true, some true, some false)
#guard cmov .e (.mem { base := .rsi }) false true == some (0xfedcba9876543210, some false, some true, some true, some false)
#guard cmov .ne (.mem { base := .rsi }) false true == some (0x1111111111111111, some false, some true, some true, some false)
#guard cmov .b (.reg .rcx) true false == some (0xfedcba9876543210, some true, some false, some true, some false)
#guard cmov .ae (.reg .rcx) true false == some (0x1111111111111111, some true, some false, some true, some false)
#guard cmov .e (.reg .rcx) true false == some (0x1111111111111111, some true, some false, some true, some false)
#guard cmov .ne (.reg .rcx) true false == some (0xfedcba9876543210, some true, some false, some true, some false)
#guard cmov .b (.mem { base := .rsi }) true false == some (0xfedcba9876543210, some true, some false, some true, some false)
#guard cmov .ae (.mem { base := .rsi }) true false == some (0x1111111111111111, some true, some false, some true, some false)
#guard cmov .e (.mem { base := .rsi }) true false == some (0x1111111111111111, some true, some false, some true, some false)
#guard cmov .ne (.mem { base := .rsi }) true false == some (0xfedcba9876543210, some true, some false, some true, some false)
#guard cmov .b (.reg .rcx) true true == some (0xfedcba9876543210, some true, some true, some true, some false)
#guard cmov .ae (.reg .rcx) true true == some (0x1111111111111111, some true, some true, some true, some false)
#guard cmov .e (.reg .rcx) true true == some (0xfedcba9876543210, some true, some true, some true, some false)
#guard cmov .ne (.reg .rcx) true true == some (0x1111111111111111, some true, some true, some true, some false)
#guard cmov .b (.mem { base := .rsi }) true true == some (0xfedcba9876543210, some true, some true, some true, some false)
#guard cmov .ae (.mem { base := .rsi }) true true == some (0x1111111111111111, some true, some true, some true, some false)
#guard cmov .e (.mem { base := .rsi }) true true == some (0xfedcba9876543210, some true, some true, some true, some false)
#guard cmov .ne (.mem { base := .rsi }) true true == some (0x1111111111111111, some true, some true, some true, some false)

-- Only the destination changes, whether or not the condition holds.
#guard (exec (.cmov .b .r8 (.reg .rcx)) (s 5 true false false false)).map
  (fun t => (t.gpr .rcx, t.gpr .rsi, t.gpr .rax, t.mem 0x1000)) == some (5, 0x1000, 0xcccccccccccccccc, 0x10)
-- The source may be the destination.
#guard (exec (.cmov .e .rcx (.reg .rcx)) (s 5 false true false false)).map (·.gpr .rcx) == some 5
-- The memory source is accessed whether or not the condition holds, and
-- a source outside the readable regions faults even when it does not.
#guard addrs (.cmov .b .r8 (.mem { base := .rsi })) (s 5 true false false false) == [0x1000]
#guard addrs (.cmov .b .r8 (.mem { base := .rsi })) (s 5 false false false false) == [0x1000]
#guard addrs (.cmov .ne .r8 (.reg .rcx)) (s 5 false false false false) == []
#guard (exec (.cmov .b .r8 (.mem { base := .rsi, disp := 8 })) (s 5 true false false false)).isNone
#guard (exec (.cmov .b .r8 (.mem { base := .rsi, disp := 8 })) (s 5 false false false false)).isNone
#guard (exec (.cmov .b .r8 (.mem { base := .rsi, disp := 1 })) (s 5 false false false false)).isNone
-- An immediate source does not exist.
#guard (exec (.cmov .b .r8 (.imm 1)) (s 5 true false false false)).isNone
#guard (exec (.cmov .ae .r8 (.imm 1)) (s 5 true false false false)).isNone
-- A condition on an undefined flag faults, as a branch on it does; the
-- other flag may be undefined.
#guard (exec (.cmov .b .r8 (.reg .rcx)) { (s 5 false false false false) with cf := none }).isNone
#guard (exec (.cmov .ae .r8 (.reg .rcx)) { (s 5 false false false false) with cf := none }).isNone
#guard (exec (.cmov .e .r8 (.reg .rcx)) { (s 5 false false false false) with zf := none }).isNone
#guard (exec (.cmov .ne .r8 (.reg .rcx)) { (s 5 false false false false) with zf := none }).isNone
#guard (exec (.cmov .b .r8 (.reg .rcx)) { (s 5 false false false false) with zf := none }).isSome
#guard (exec (.cmov .e .r8 (.reg .rcx)) { (s 5 false false false false) with cf := none }).isSome
#guard (exec (.cmov .e .r8 (.reg .rcx))
  { (s 5 false false false false) with sf := none, of := none }).isSome

/-! ## Printing -/

#guard printer.instr (.shift .shl .rcx 4) == ["shl rcx, 4"]
#guard printer.instr (.shift .shl .r15 63) == ["shl r15, 63"]
#guard printer.instr (.shift32 .shl .rcx 31) == ["shl ecx, 31"]
#guard printer.instr (.shift32 .shl .r9 1) == ["shl r9d, 1"]
#guard printer.instr (.cmov .b .r8 (.reg .rcx)) == ["cmovb r8, rcx"]
#guard printer.instr (.cmov .ae .rax (.reg .r15)) == ["cmovae rax, r15"]
#guard printer.instr (.cmov .e .r13 (.mem { base := .rsi, disp := 8 })) ==
  ["cmove r13, QWORD PTR [rsi+8]"]
#guard printer.instr (.cmov .ne .rdx (.mem { base := .rdi, index := some .rcx, scale := 8 })) ==
  ["cmovne rdx, QWORD PTR [rdi+rcx*8]"]

-- Neither needs a CPU feature beyond the baseline; each writes `rsp` if
-- its destination is `rsp`.
#guard isa.requires (.shift .shl .rax 1) == []
#guard isa.requires (.shift32 .shl .rax 1) == []
#guard [Cond.e, .ne, .b, .ae].all fun c => isa.requires (.cmov c .rax (.reg .rbx)) == []
#guard isa.writesSp (.cmov .b .rsp (.reg .rax))
#guard !isa.writesSp (.cmov .b .rax (.reg .rsp))
#guard isa.writesSp (.shift .shl .rsp 3)

end VG.Test.X86_64ShlCmov
