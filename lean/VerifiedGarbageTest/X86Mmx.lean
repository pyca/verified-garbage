import VerifiedGarbage.TCB.X86.Print

/-!
# IA-32 MMX transcription tests

The inputs are those of `VerifiedGarbageTest/X86Sse.lean`; the expected
results were computed with the native intrinsics (`_mm_add_si64`,
`_mm_xor_si64`, `_mm_or_si64`, `_mm_and_si64`, `_mm_andnot_si64`,
`_mm_slli_si64`, `_mm_srli_si64`, `_mm_unpacklo_pi32`, `_mm_cvtsi32_si64`,
`_mm_movpi64_epi64`, `_mm_movepi64_pi64`). They cover the MMX frame (the
instructions fault outside one; its push and pop), memory permissions,
printing and CPU requirements. These are ISA transcription tests, not
primitive known-answer vectors.
-/

namespace VG.Test.X86Mmx

open X86

def a : BitVec 64 := 0xfedcba9876543210#64
def b : BitVec 64 := 0x7fffffff12345678#64
def x : BitVec 128 := 0x89abcdef01234567fedcba9876543210#128

/-- Inside an MMX frame, with `mm0 = a`, `mm1 = b`, `xmm0 = x`. -/
def s : State where
  gpr r := if r = .edi then 0x100 else if r = .eax then 0xdeadbeef else if r = .esp then 0x1000 else 0
  cf := some true
  zf := some false
  sf := some true
  of := some false
  xmm r := if r = .xmm0 then x else 0
  mm r := if r = .mm0 then a else if r = .mm1 then b else 0
  mmx := true
  mem addr := if 0x100 ≤ addr.toNat ∧ addr.toNat < 0x110 then
    BitVec.ofNat 8 (17 * (addr.toNat - 0x100) + 3) else 0
  rd := [⟨0x100, 16⟩]
  wr := [⟨0x200, 16⟩]

/-- `mm0` after `op` in `s`. -/
def mm0 (op : MOp) : Option (BitVec 64) := (op.exec s).map (·.mm .mm0)

#guard mm0 (.bin .paddq .mm0 (.reg .mm1)) == some 0x7edcba9788888888#64
#guard mm0 (.bin .pxor .mm0 (.reg .mm1)) == some 0x8123456764606468#64
#guard mm0 (.bin .por .mm0 (.reg .mm1)) == some 0xffffffff76747678#64
#guard mm0 (.bin .pand .mm0 (.reg .mm1)) == some 0x7edcba9812141210#64
#guard mm0 (.bin .pandn .mm0 (.reg .mm1)) == some 0x0123456700204468#64
#guard mm0 (.shift .psllq .mm0 13) == some 0x97530eca86420000#64
#guard mm0 (.shift .psrlq .mm0 13) == some 0x0007f6e5d4c3b2a1#64
#guard mm0 (.shift .psllq .mm0 63) == some 0
#guard mm0 (.shift .psrlq .mm0 63) == some 1
#guard mm0 (.shift .psllq .mm0 64) == some 0
#guard mm0 (.shift .psrlq .mm0 255) == some 0
#guard mm0 (.punpckldq .mm0 .mm1) == some 0x1234567876543210#64
#guard mm0 (.movd .mm0 .eax) == some 0x00000000deadbeef#64
#guard mm0 (.movq .mm0 (.reg .mm1)) == some b
#guard mm0 (.movdq2q .mm0 .xmm0) == some 0xfedcba9876543210#64
#guard ((MOp.movq2dq .xmm1 .mm1).exec s).map (·.xmm .xmm1) ==
  some 0x00000000000000007fffffff12345678#128
-- `paddq` wraps within the quadword.
#guard ((MOp.bin .paddq .mm2 (.reg .mm3)).exec
  { s with mm := fun r => if r = .mm2 then -1 else if r = .mm3 then 1 else 0 }).map (·.mm .mm2) == some 0
-- Only the destination changes, and no flag or general-purpose register.
#guard ((MOp.bin .paddq .mm0 (.reg .mm1)).exec s).map (·.mm .mm1) == some b
#guard ((MOp.bin .pxor .mm0 (.reg .mm1)).exec s).map (·.gpr .eax) == some (s.gpr .eax)
#guard ((MOp.shift .psllq .mm0 1).exec s).map (·.cf) == some s.cf
#guard ((MOp.movq2dq .xmm1 .mm1).exec s).map (·.xmm .xmm0) == some x

-- Memory sources: 8 bytes, little-endian, within the readable regions only.
#guard mm0 (.movq .mm0 (.mem { base := .edi })) == some 0x7a69584736251403#64
#guard mm0 (.movq .mm0 (.mem { base := .edi, disp := 8 })) == some 0x02f1e0cfbead9c8b#64
#guard mm0 (.movq .mm0 (.mem { base := .edi, disp := 9 })) == none
#guard mm0 (.bin .pxor .mm0 (.mem { base := .edi })) == some (a ^^^ 0x7a69584736251403#64)
#guard (MOp.addrs (.bin .paddq .mm0 (.mem { base := .edi, disp := 4 })) s) == [0x104]
-- The 8-byte store, within the writable regions only.
#guard ((exec (.mmxStore { base := .edi, disp := 0x108 } .mm0) s).map
  (·.mem.readW 0x208 64)) == some a
#guard ((exec (.mmxStore { base := .edi, disp := 0x100 } .mm0) s).map
  (·.mem.readW 0x208 64)) == some (s.mem.readW 0x208 64)
#guard (exec (.mmxStore { base := .edi, disp := 0x109 } .mm0) s).isNone
#guard (exec (.mmxStore { base := .edi } .mm0) s).isNone

/-! ## The MMX frame -/

/-- `s` outside an MMX frame. -/
def s₀ : State := { s with mmx := false }

-- Every MMX instruction faults outside an MMX frame.
#guard ((MOp.bin .paddq .mm0 (.reg .mm1)).exec s₀).isNone
#guard ((MOp.shift .psllq .mm0 1).exec s₀).isNone
#guard ((MOp.movq .mm0 (.reg .mm1)).exec s₀).isNone
#guard ((MOp.punpckldq .mm0 .mm1).exec s₀).isNone
#guard ((MOp.movd .mm0 .eax).exec s₀).isNone
#guard ((MOp.movq2dq .xmm1 .mm1).exec s₀).isNone
#guard ((MOp.movdq2q .mm0 .xmm0).exec s₀).isNone
#guard (exec (.mmxStore { base := .edi, disp := 0x108 } .mm0) s₀).isNone
-- The frame's push and pop are not instructions on their own.
#guard (exec .mmxEnter s₀).isNone
#guard (exec .emms s).isNone

/-- The state after the push of an MMX frame. -/
def s₁ : Option State := isa.push .mmxEnter s₀

-- The push enters MMX mode with an empty frame at `esp`, and moves no `esp`.
#guard s₁.map (·.mmx) == some true
#guard s₁.map (·.wr) == some (⟨0x1000, 0⟩ :: s₀.wr)
#guard s₁.map (·.gpr .esp) == some 0x1000
#guard s₁.map (·.mm .mm0) == some a
-- MMX frames do not nest.
#guard (isa.push .mmxEnter s).isNone
-- `emms` leaves the frame, removing it, when `esp` and the regions are those
-- the push left; otherwise it faults.
#guard (s₁.bind fun t => isa.pop .emms t t).map (fun t => (t.mmx, t.wr)) == some (false, s₀.wr)
#guard (s₁.bind fun t => isa.pop .emms t { t with mmx := false }).isNone
#guard (s₁.bind fun t => isa.pop .emms t (t.setReg .esp 0xffc)).isNone
#guard (s₁.bind fun t => isa.pop .emms t { t with wr := s₀.wr }).isNone
#guard (isa.pop .emms s s).isNone

/-! ## Printing and feature declarations -/
#guard printer.instr (.mop (.bin .paddq .mm0 (.reg .mm1))) == ["paddq mm0, mm1"]
#guard printer.instr (.mop (.bin .pxor .mm2 (.mem { base := .esp, disp := 8 }))) ==
  ["pxor mm2, QWORD PTR [esp+8]"]
#guard printer.instr (.mop (.bin .por .mm3 (.reg .mm4))) == ["por mm3, mm4"]
#guard printer.instr (.mop (.bin .pand .mm5 (.reg .mm6))) == ["pand mm5, mm6"]
#guard printer.instr (.mop (.bin .pandn .mm7 (.reg .mm0))) == ["pandn mm7, mm0"]
#guard printer.instr (.mop (.shift .psllq .mm1 23)) == ["psllq mm1, 23"]
#guard printer.instr (.mop (.shift .psrlq .mm2 41)) == ["psrlq mm2, 41"]
#guard printer.instr (.mop (.movq .mm3 (.reg .mm4))) == ["movq mm3, mm4"]
#guard printer.instr (.mop (.movq .mm5 (.mem { base := .esi, disp := 16 }))) ==
  ["movq mm5, QWORD PTR [esi+16]"]
#guard printer.instr (.mop (.punpckldq .mm6 .mm7)) == ["punpckldq mm6, mm7"]
#guard printer.instr (.mop (.movd .mm0 .eax)) == ["movd mm0, eax"]
#guard printer.instr (.mop (.movq2dq .xmm1 .mm2)) == ["movq2dq xmm1, mm2"]
#guard printer.instr (.mop (.movdq2q .mm3 .xmm4)) == ["movdq2q mm3, xmm4"]
#guard printer.instr (.mmxStore { base := .edi, disp := 24 } .mm5) == ["movq QWORD PTR [edi+24], mm5"]
#guard printer.instr .mmxEnter == []
#guard printer.instr .emms == ["emms"]
-- All MMX or SSE2: the baseline.
#guard isa.requires (.mop (.bin .paddq .mm0 (.reg .mm1))) == []
#guard isa.requires (.mop (.movq2dq .xmm1 .mm2)) == []
#guard isa.requires (.mmxStore { base := .edi } .mm5) == []
#guard isa.requires .mmxEnter == [] && isa.requires .emms == []
-- None writes `esp`.
#guard !isa.writesSp (.mop (.movd .mm0 .esp))
#guard !isa.writesSp (.mmxStore { base := .esp } .mm0)
#guard !isa.writesSp .mmxEnter && !isa.writesSp .emms

end VG.Test.X86Mmx
