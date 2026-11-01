module

import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Golden tests for the RISC-V instruction semantics

The ISA model is part of the TCB; these tests run each instruction on a
concrete state, so that the values they compute (in particular the 32-bit
`*w` forms, which sign-extend, the zero-extending loads and the sign
extension of immediates) and when they fault show up in review. The
expected values were checked against the same instructions run under QEMU's
riscv64 emulation (`qemu-riscv64`), from the same registers and memory.
-/

namespace VG.Test.RISCV64

open VG.RISCV64

/-- `a0` points to 16 readable and writable bytes `0x80, 0x81, …, 0x8f` at
`0x1000`; `a1 = 0x8000_0001_f000_0001`, `a2 = 4`, `a3 = 0xffff_ffff_0123_4567`. -/
def s0 : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x80000001f0000001 | .a2 => 4 | .a3 => 0xffffffff01234567 | _ => 0
  sp := 0x2000
  mem a := a.setWidth 8 ^^^ 0x80
  rd := []
  wr := [⟨0x1000, 16⟩]

/-- `a4` after running `i` (the destination of every test). -/
def reg (i : Instr) : Option (BitVec 64) := (exec i s0).map (·.gpr .a4)

-- 64-bit arithmetic, comparison and logic.
#guard reg (.add .a4 .a1 .a3) == some 0x80000000f1234568
#guard reg (.sub .a4 .a2 .a1) == some 0x7ffffffe10000003
#guard reg (.sltu .a4 .a2 .a1) == some 1
#guard reg (.sltu .a4 .a1 .a2) == some 0
#guard reg (.sltu .a4 .a1 .a1) == some 0
#guard reg (.logic .and .a4 .a1 .a3) == some 0x8000000100000001
#guard reg (.logic .or .a4 .a1 .a2) == some 0x80000001f0000005
#guard reg (.logic .xor .a4 .a1 .a3) == some 0x7ffffffef1234566
-- Multiplies: the low 64 bits of the product, and the high 64 bits of the
-- unsigned product (`a1` and `a3` have their top bits set, so a signed
-- `mulh` would differ).
#guard reg (.mul .a4 .a1 .a3) == some 0x9234567691234567
#guard reg (.mulhu .a4 .a1 .a3) == some 0x800000017091a2b2
#guard reg (.mulhu .a4 .a3 .a2) == some 0x3
#guard reg (.mul .a4 .a3 .a2) == some 0xfffffffc048d159c
-- 32-bit arithmetic: the low words, the result sign-extended.
#guard reg (.addw .a4 .a1 .a3) == some 0xfffffffff1234568
#guard reg (.subw .a4 .a2 .a1) == some 0x10000003
-- Immediates are 12 bits, sign-extended.
#guard reg (.addi .a4 .a3 2047) == some 0xffffffff01234d66
#guard reg (.addi .a4 .a2 (-5)) == some 0xffffffffffffffff
#guard reg (.addi .a4 .a2 (-2048)) == some 0xfffffffffffff804
#guard reg (.addiw .a4 .a3 (-1)) == some 0x01234566
#guard reg (.addiw .a4 .a1 2047) == some 0xfffffffff0000800
#guard reg (.addiw .a4 .a3 0) == some 0x01234567
#guard reg (.logicImm .and .a4 .a1 (-1)) == some 0x80000001f0000001
#guard reg (.logicImm .and .a4 .a3 2047) == some 0x567
#guard reg (.logicImm .or .a4 .a2 (-2048)) == some 0xfffffffffffff804
#guard reg (.logicImm .xor .a4 .a3 (-1)) == some 0xfedcba98
#guard reg (.li .a4 (-1)) == some 0xffffffffffffffff
#guard reg (.li .a4 2047) == some 0x7ff
#guard (reg (.addi .a4 .a3 2048)).isNone && (reg (.addi .a4 .a3 (-2049))).isNone &&
  (reg (.addiw .a4 .a3 2048)).isNone && (reg (.logicImm .or .a4 .a3 2048)).isNone &&
  (reg (.li .a4 (-2049))).isNone
-- `lui` sign-extends its 32-bit result.
#guard reg (.lui .a4 0x7ffff) == some 0x7ffff000
#guard reg (.lui .a4 0x80000) == some 0xffffffff80000000
#guard reg (.lui .a4 0x12345) == some 0x12345000

-- Doubleword shifts.
#guard reg (.shift .sll .d .a4 .a3 32) == some 0x0123456700000000
#guard reg (.shift .srl .d .a4 .a1 60) == some 0x8
#guard reg (.shift .sra .d .a4 .a1 60) == some 0xfffffffffffffff8
#guard reg (.shift .sra .d .a4 .a3 4) == some 0xfffffffff0123456
-- Word shifts read the low word and sign-extend the result, even a logical
-- shift right by 0.
#guard reg (.shift .sll .w .a4 .a1 4) == some 0x10
#guard reg (.shift .sll .w .a4 .a3 7) == some 0xffffffff91a2b380
#guard reg (.shift .srl .w .a4 .a1 4) == some 0x0f000000
#guard reg (.shift .srl .w .a4 .a1 0) == some 0xfffffffff0000001
#guard reg (.shift .sra .w .a4 .a1 4) == some 0xffffffffff000000
#guard reg (.shift .sra .w .a4 .a3 0) == some 0x01234567
#guard (reg (.shift .sll .d .a4 .a1 64)).isNone && (reg (.shift .srl .w .a4 .a1 32)).isNone
-- Shifts by a register: by its low 6 bits (doublewords) or low 5 bits
-- (words). `a3`'s low byte is `0x67`, so it shifts a doubleword by 39 and a
-- word by 7; `a1`'s is 1, `a2`'s 4 and `a5` is 0. (These expected values
-- were computed from the manual's definitions by a separate Python model.)
#guard reg (.shiftReg .sll .d .a4 .a3 .a2) == some 0xfffffff012345670
#guard reg (.shiftReg .sll .d .a4 .a1 .a3) == some 0x8000000000
#guard reg (.shiftReg .srl .d .a4 .a1 .a3) == some 0x1000000
#guard reg (.shiftReg .sra .d .a4 .a1 .a3) == some 0xffffffffff000000
#guard reg (.shiftReg .srl .d .a4 .a3 .a1) == some 0x7fffffff8091a2b3
#guard reg (.shiftReg .sra .d .a4 .a3 .a2) == some 0xfffffffff0123456
#guard reg (.shiftReg .sll .w .a4 .a1 .a2) == some 0x10
#guard reg (.shiftReg .sll .w .a4 .a3 .a3) == some 0xffffffff91a2b380
#guard reg (.shiftReg .srl .w .a4 .a1 .a2) == some 0x0f000000
#guard reg (.shiftReg .srl .w .a4 .a1 .a5) == some 0xfffffffff0000001
#guard reg (.shiftReg .srl .w .a4 .a3 .a1) == some 0x0091a2b3
#guard reg (.shiftReg .sra .w .a4 .a1 .a2) == some 0xffffffffff000000
#guard reg (.shiftReg .sra .w .a4 .a3 .a3) == some 0x0002468a

-- Loads are little-endian and zero-extended.
#guard reg (.load .b .a4 .a0 15) == some 0x8f
#guard reg (.load .h .a4 .a0 2) == some 0x8382
#guard reg (.load .w .a4 .a0 4) == some 0x87868584
#guard reg (.load .d .a4 .a0 8) == some 0x8f8e8d8c8b8a8988
-- Out of the permitted regions, misaligned, or with an unencodable displacement.
#guard (reg (.load .d .a4 .a0 16)).isNone
#guard (reg (.load .d .a4 .a0 4)).isNone && (reg (.load .w .a4 .a0 2)).isNone &&
  (reg (.load .h .a4 .a0 1)).isNone
#guard (reg (.load .b .a4 .a0 2048)).isNone
#guard (reg (.load .b .a4 .a0 16)).isNone

def mem (i : Instr) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  (exec i s0).map (·.mem.read a n)

-- Stores: the low bytes, little-endian.
#guard mem (.store .w .a3 .a0 0) 0x1000 8 == some 0x8786858401234567
#guard mem (.store .d .a1 .a0 8) 0x1008 8 == some 0x80000001f0000001
#guard mem (.store .b .a3 .a0 3) 0x1000 8 == some 0x8786858467828180
#guard mem (.store .h .a3 .a0 6) 0x1000 8 == some 0x4567858483828180
#guard (mem (.store .w .a3 .a0 16) 0x1000 1).isNone && (mem (.store .w .a3 .a0 2) 0x1000 1).isNone
-- Stores need a writable region.
#guard ((exec (.store .b .a3 .a0 0) { s0 with rd := s0.wr, wr := [] }).map (·.mem.read 0x1000 1)).isNone
#guard ((exec (.load .b .a4 .a0 0) { s0 with rd := s0.wr, wr := [] }).map (·.gpr .a4)) == some 0x80

-- Conditions compare a register with zero, or two registers.
#guard eval (.zero .a1) s0 == some false && eval (.zero .a4) s0 == some true
#guard eval (.nonzero .a1) s0 == some true && eval (.nonzero .a4) s0 == some false
#guard eval (.eq .a1 .a1) s0 == some true && eval (.eq .a1 .a2) s0 == some false
#guard eval (.ne .a1 .a2) s0 == some true && eval (.ne .a2 .a2) s0 == some false
-- Unsigned: `a1`, with its top bit set, is above `a2`.
#guard eval (.ltu .a2 .a1) s0 == some true && eval (.ltu .a1 .a2) s0 == some false &&
  eval (.ltu .a2 .a2) s0 == some false
#guard eval (.geu .a1 .a2) s0 == some true && eval (.geu .a2 .a1) s0 == some false &&
  eval (.geu .a2 .a2) s0 == some true

-- A call leaves the next unknown values in `ra` and `t0`–`t6`; the return
-- only goes back to that address.
def sCall : State := { s0 with unknowns := fun n => BitVec.ofNat 64 (n + 100) }
#guard (call sCall).map (fun s => ([.ra, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .s0].map s.gpr,
    s.unknowns 0)) == some ([100, 101, 102, 103, 104, 105, 106, 107, 0x1000, 0], 108)
#guard ((call sCall).bind fun s₁ => (ret s₁ s₁).map (·.gpr .ra)) == some 100
#guard ((call sCall).bind fun s₁ => ret s₁ (s₁.write .ra 0)).isNone

-- `lla` writes the address of the static it names to its register, and
-- nothing else.
def sSym : State := { s0 with syms := fun n => if n = "VG_TABLE" then 0x12340 else 0x5000 }
#guard (exec (.lla .a4 "VG_TABLE") sSym).map (fun s => ([.a4, .a0, .a1, .a2, .a3].map s.gpr,
    s.sp, s.mem.read 0x1000 16, s.rd, s.wr, s.syms "VG_TABLE")) ==
  some ([0x12340, 0x1000, 0x80000001f0000001, 4, 0xffffffff01234567], 0x2000,
    s0.mem.read 0x1000 16, [], [⟨0x1000, 16⟩], 0x12340)
#guard (exec (.lla .a4 "VG_OTHER") sSym).map (·.gpr .a4) == some 0x5000

end VG.Test.RISCV64
