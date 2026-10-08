import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffer
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

private theorem store32_eq (s : State) (a : Addr) (v : BitVec 32) :
    s.store32 a v = if InRegions s.wr a 4 then some (s.setMem (s.mem.writeW a v)) else none := rfl

def finishHead : List Instr :=
  [.mov .rax (.reg .rsi), .alu32 .sub .r8 (.imm 8), .bswap32 .r8,
   .store32 (at_ .rax 12) .r8, .vmovdquLoad .l128 .xmm0 (at_ .r11 768)]

theorem finishHead_ok (s : State)
    (hw : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 12) 4)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 768) 16)
    (hs : Mem.Sep (s.gpr .r11 + BitVec.ofNat 64 768) 16 (s.gpr .rsi + BitVec.ofNat 64 12) 4) :
    WP isa (.block finishHead) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 12) (bswap32 ((s.gpr .r8).setWidth 32 - 8)) ∧
      t.lane .xmm0 0 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 768) 128 ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm0 → ∀ l < 2, t.lane r l = s.lane r l) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [finishHead, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc, readSrc32, execAlu32, State.setReg32, store32_eq, State.load128,
    ea_at, BitVec.ofInt_natCast, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    State.setMem_gpr, State.setMem_mem, State.setMem_rd, State.setMem_wr,
    setWidth_setWidth_32, reduceCtorEq, ↓reduceIte, hw, hr, Option.map_some, Option.bind_some,
    Mem.readW_writeW_sep (w := 128) (w' := 32) hs (by decide), Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.lane, xmm_setV, ite_true]
  · intro r hax h8
    simp only [State.setV_gpr, State.setMem_gpr, gpr_setReg, gpr_arithFlags, hax, h8, ite_false]
  · intro r hr l hl
    simp only [State.lane, xmm_setV, ymmHi_setV_128, State.setMem_xmm, State.setMem_ymmHi,
      xmm_setReg, ymmHi_setReg, xmm_arithFlags, ymmHi_arithFlags, hr, ite_false]
  · rfl
  · rfl

def restoreEntry : List Instr :=
  [.mov .r8 (.mem (at_ .r11 808)), .mov .rsi (.mem (at_ .r11 800))]

theorem restoreEntry_ok (s : State)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 808) 8)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 800) 8) :
    WP isa (.block restoreEntry) s fun t =>
      t.gpr .r8 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 808) 64 ∧
      t.gpr .rsi = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 800) 64 ∧
      (∀ r, r ≠ .r8 → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [restoreEntry, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc, State.load64, ea_at, BitVec.ofInt_natCast, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
    reduceCtorEq, ↓reduceIte, h8, hi, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, trivial, trivial, trivial⟩
  intro r h8 hi
  simp only [h8, hi, ite_false]

end VG.Proof.Gcm.X86_64.StitchAvx8
