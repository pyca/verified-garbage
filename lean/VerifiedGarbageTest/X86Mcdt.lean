import VerifiedGarbage.TCB.X86.Print

/-!
# IA-32 PMULUDQ and MCDT frame transcription tests

The expected products were computed with the native intrinsic
(`_mm_mul_epu32`, compiled with `gcc -m32 -msse2`). They cover the MCDT
frame (`pmuludq` faults outside one; its push and pop, which restore
MXCSR, nest, and pair with no other frame's), the addresses it leaks,
printing and CPU requirements. These are ISA transcription tests, not primitive known-answer
vectors.
-/

namespace VG.Test.X86Mcdt

open X86

def x : BitVec 128 := 0x89abcdef01234567fedcba9876543210#128
def y : BitVec 128 := 0x0123456789abcdefffffffff00000002#128
def m : BitVec 128 := 0x00000000ffffffffffffffffffffffff#128

-- SDM: the products of doublewords 0 and 2, as `_mm_mul_epu32` computes them.
#guard pmuludq x y == 0x009ca39dc94e462900000000eca86420#128
#guard pmuludq y x == 0x009ca39dc94e462900000000eca86420#128
#guard pmuludq m m == 0xfffffffe00000001fffffffe00000001#128

/-- Outside an MCDT frame, with `xmm0 = x`, `xmm1 = y`, `esp = 0x1000`, and
the 16 bytes below `esp` writable. -/
def s₀ : State where
  gpr r := if r = .esp then 0x1000 else if r = .eax then 0xdeadbeef else 0
  cf := some true
  zf := some false
  sf := some true
  of := some false
  xmm r := if r = .xmm0 then x else if r = .xmm1 then y else 0
  mxcsr := 0x1f80
  mem _ := 0
  rd := []
  wr := [⟨0xff0, 16⟩]

-- `pmuludq` faults outside an MCDT frame, and runs inside one.
#guard (exec (.pmuludq .xmm0 .xmm1) s₀).isNone
#guard (exec (.pmuludq .xmm0 .xmm1) { s₀ with mcdt := 1 }).map (·.xmm .xmm0) ==
  some 0x009ca39dc94e462900000000eca86420#128
-- Only the destination changes.
#guard (exec (.pmuludq .xmm0 .xmm1) { s₀ with mcdt := 1 }).map (·.xmm .xmm1) == some y
#guard (exec (.pmuludq .xmm0 .xmm1) { s₀ with mcdt := 1 }).map (·.cf) == some s₀.cf
-- The frame's push and pop are not instructions on their own.
#guard (exec (.mcdtEnter .eax) s₀).isNone
#guard (exec .mcdtLeave s₀).isNone

/-! ## The MCDT frame -/

/-- The state after the push of an MCDT frame. -/
def s₁ : Option State := isa.push (.mcdtEnter .eax) s₀

-- The push takes 12 bytes below `esp`, saves MXCSR at `esp + 4` and `0x1FBF`
-- (from `eax`) at `esp`, and opens the frame, whose region is 9 bytes.
#guard s₁.map (·.gpr .esp) == some 0xff4
#guard s₁.map (·.gpr .eax) == some 0x1fbf
#guard s₁.map (·.wr) == some (⟨0xff4, 9⟩ :: s₀.wr)
#guard s₁.map (·.mem.readW 0xff8 32) == some 0x1f80
#guard s₁.map (·.mem.readW 0xff4 32) == some 0x1fbf
#guard s₁.map (·.mcdt) == some 1
#guard s₁.map (·.mxcsr) == some 0x1f80
#guard s₁.map (·.cf) == some s₀.cf
-- It accesses the two words at its bottom: `stmxcsr`, then `mov` and `ldmxcsr`.
#guard addrs (.mcdtEnter .eax) s₀ == [0xff8, 0xff4, 0xff4]
-- `esp` cannot hold `0x1FBF`; the frame cannot wrap.
#guard (isa.push (.mcdtEnter .esp) s₀).isNone
#guard (isa.push (.mcdtEnter .eax) (s₀.setReg .esp 8)).isNone
-- A nested frame saves `0x1FBF`, the value MXCSR holds inside the outer one.
#guard (s₁.bind fun t => isa.push (.mcdtEnter .ecx) t).map (fun t => (t.mcdt, t.mem.readW 0xfec 32)) ==
  some (2, 0x1fbf)
-- The pop restores `esp`, removes the frame and closes it, when `esp`, the
-- regions and the saved word are those the push left.
#guard (s₁.bind fun t => isa.pop .mcdtLeave t t).map (fun t => (t.mcdt, t.wr, t.gpr .esp)) ==
  some (0, s₀.wr, 0x1000)
#guard addrs .mcdtLeave (s₀.setReg .esp 0xff4) == [0xff8]
-- It faults if the saved word no longer holds MXCSR,
#guard (s₁.bind fun t => isa.pop .mcdtLeave t { t with mem := t.mem.writeW 0xff8 (0x1fbf : BitVec 32) }).isNone
-- with no frame open, or with another `esp` or other regions.
#guard (s₁.bind fun t => isa.pop .mcdtLeave t { t with mcdt := 0 }).isNone
#guard (s₁.bind fun t => isa.pop .mcdtLeave t (t.setReg .esp 0xff0)).isNone
#guard (s₁.bind fun t => isa.pop .mcdtLeave t { t with wr := s₀.wr }).isNone
#guard (isa.pop .mcdtLeave s₀ s₀).isNone
-- No other pop removes an MCDT frame, and `mcdtLeave` removes no other frame.
#guard (s₁.bind fun t => isa.pop (.free 8) t t).isNone
#guard (s₁.bind fun t => isa.pop (.free 12) t t).isNone
#guard (s₁.bind fun t => isa.pop (.pop .ecx 3) t t).isNone
#guard (s₁.bind fun t => isa.pop .emms t { t with mmx := true }).isNone
#guard ((isa.push (.alloc 12) { s₀ with mcdt := 1 }).bind fun t => isa.pop .mcdtLeave t t).isNone
#guard ((isa.push .mmxEnter { s₀ with mcdt := 1 }).bind fun t => isa.pop .mcdtLeave t t).isNone

/-! ## Printing and feature declarations -/

#guard Instr.asm (.pmuludq .xmm2 .xmm7) == ["pmuludq xmm2, xmm7"]
#guard Instr.asm (.mcdtEnter .ecx) == ["lea esp, [esp-12]", "stmxcsr DWORD PTR [esp+4]",
  "mov ecx, 8127", "mov DWORD PTR [esp], ecx", "ldmxcsr DWORD PTR [esp]", "lfence"]
#guard Instr.asm .mcdtLeave == ["lfence", "ldmxcsr DWORD PTR [esp+4]", "lea esp, [esp+12]"]
#guard Instr.requires (.pmuludq .xmm0 .xmm1) == []
#guard Instr.requires (.mcdtEnter .eax) == []
#guard Instr.requires .mcdtLeave == []

end VG.Test.X86Mcdt
