import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `imul r64, r64`

Each expected value was computed on an x86-64 CPU, by the same instruction
(`imul rax, rcx` or `imul rax, rax` in inline assembly, reading RFLAGS with
`pushfq` after it), and is compared with the model's result on the same
inputs. This tests the transcription of the SDM's pseudocode (the low half of
the product, and CF and OF set when the signed product does not fit), which
review of the TCB would otherwise have to catch by eye.
-/

namespace VG.Test.X86_64Imul

open X86_64

/-- A state with `a` in `rax` and `b` in `rcx`, and every flag defined. -/
def s (a b : BitVec 64) : State where
  gpr r := if r = .rax then a else if r = .rcx then b else 7
  cf := some false
  zf := some true
  sf := some true
  of := some false
  mem _ := 0
  rd := []
  wr := []

/-- `rax`, CF and OF after `imul rax, src`, and whether SF and ZF are undefined. -/
def run (src : Reg) (a b : BitVec 64) : Option (BitVec 64 × Option Bool × Option Bool × Bool) :=
  (exec (.imul .rax src) (s a b)).map fun t => (t.gpr .rax, t.cf, t.of, t.sf.isNone && t.zf.isNone)

/-- `imul rax, rcx` with `a` in `rax` and `b` in `rcx`: the expected product
and CF (= OF). -/
def imulRcx (a b p : BitVec 64) (c : Bool) : Bool :=
  run .rcx a b == some (p, some c, some c, true)

#guard imulRcx 0x0 0x0 0x0 false
#guard imulRcx 0x3 0x5 0xf false
#guard imulRcx 0xffffffffffffffff 0x2 0xfffffffffffffffe false
#guard imulRcx 0xffffffffffffffff 0xffffffffffffffff 0x1 false
#guard imulRcx 0x123456789abcdef 0xfedcba9876543210 0x2236d88fe5618cf0 true
#guard imulRcx 0x8000000000000000 0x1 0x8000000000000000 false
#guard imulRcx 0x8000000000000000 0xffffffffffffffff 0x8000000000000000 true
#guard imulRcx 0x7fffffffffffffff 0x2 0xfffffffffffffffe true
#guard imulRcx 0x4000000000000000 0x2 0x8000000000000000 true
#guard imulRcx 0xc000000000000000 0x2 0x8000000000000000 false
#guard imulRcx 0xdeadbeefcafebabe 0x100000001 0xa9ac79adcafebabe true
#guard imulRcx 0xffffffff 0xffffffff 0xfffffffe00000001 true
#guard imulRcx 0x100000000 0x100000000 0x0 true

-- `imul rax, rax` squares `rax`.
#guard run .rax 0xdeadbeefcafebabe 0 == some (0xb295b2eef140a504, some true, some true, true)

-- Only the destination and the flags change.
#guard (exec (.imul .rax .rcx) (s 3 5)).map (fun t => (t.gpr .rcx, t.gpr .rdx, t.gpr .r15)) == some (5, 7, 7)

/-! ## Printing -/

#guard printer.instr (.imul .rax .rcx) == ["imul rax, rcx"]
#guard printer.instr (.imul .r11 .rdx) == ["imul r11, rdx"]

-- `imul` is in the x86-64 baseline, and writes `rsp` only as its destination.
#guard isa.requires (.imul .rax .rcx) == []
#guard isa.writesSp (.imul .rsp .rax)
#guard !isa.writesSp (.imul .rax .rsp)

end VG.Test.X86_64Imul
