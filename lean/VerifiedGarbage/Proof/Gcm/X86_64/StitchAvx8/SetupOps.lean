import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffer
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base

/-! # Pointer setup and the saved entry state -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupC)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Proof.Gcm.X86_64.Stitch (in_rdwr)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

theorem setupC_ok (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) :
    WP isa (.block setupC) s fun t =>
      t.lane .xmm2 0 = Spec.Gcm.blockAt s.mem (s.gpr .rcx) ∧
      t.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      t.gpr .rax = s.gpr .rdx ∧ t.gpr .rdx = s.gpr .r8 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → t.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → ∀ l < 2, t.lane r l = s.lane r l) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have m0 := h0
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, execShift, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide, and_self, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    ea_at, hy', VBinOp.sse, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, ?_, trivial, trivial, fun r h1 h2 h3 => ?_, fun r h2 l hl => ?_, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (blockAt_eq _ _).symm
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2]

private theorem store64_eq (s : State) (a : Addr) (v : BitVec 64) :
    s.store64 a v = if InRegions s.wr a 8 then some (s.setMem (s.mem.writeW a v)) else none := rfl

def metaCode : List Instr :=
  [.vmovdquStore .l128 (at_ .r11 768) .xmm0,
   .vmovdquStore .l128 (at_ .r11 784) .xmm1,
   .store (at_ .r11 808) .rdx, .store (at_ .r11 800) .rsi]

def metaMem (s : State) : Mem :=
  (((s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 768) (s.lane .xmm0 0)).writeW
    (s.gpr .r11 + BitVec.ofNat 64 784) (s.lane .xmm1 0)).writeW
    (s.gpr .r11 + BitVec.ofNat 64 808) (s.gpr .rdx)).writeW (s.gpr .r11 + BitVec.ofNat 64 800) (s.gpr .rsi)

theorem meta_ok (s : State)
    (h0 : InRegions s.wr (s.gpr .r11 + 768) 16)
    (h1 : InRegions s.wr (s.gpr .r11 + 784) 16)
    (h2 : InRegions s.wr (s.gpr .r11 + 808) 8)
    (h3 : InRegions s.wr (s.gpr .r11 + 800) 8) :
    WP isa (.block metaCode) s fun t => t.mem = metaMem s ∧ t.gpr = s.gpr ∧
      (∀ r l, t.lane r l = s.lane r l) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  change InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 768) 16 at h0
  change InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 784) 16 at h1
  change InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 808) 8 at h2
  change InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 800) 8 at h3
  simp only [metaCode, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    State.store128_eq, store64_eq, ea_at,
    BitVec.ofInt_natCast, h0, h1, h2, h3, ite_true,
    State.setMem_gpr, State.setMem_wr, State.setMem_xmm, State.setMem_mem, State.setMem_rd, State.setMem_lane,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun _ _ => trivial, trivial, trivial⟩

def counterHead : List Instr :=
  [.mov .rsi (.reg .rax), .vmovdquLoad .l128 .xmm7 (at_ .rax 0),
   .mov32 .r8 (.mem (at_ .rax 12)), .bswap32 .r8]

theorem counterHead_ok (s : State)
    (hc : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 0) 16)
    (hl : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 12) 4) :
    WP isa (.block counterHead) s fun t =>
      t.gpr .rsi = s.gpr .rax ∧
      (t.gpr .r8).setWidth 32 = bswap32 (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 12) 32) ∧
      t.lane .xmm7 0 = s.mem.readW (s.gpr .rax + BitVec.ofNat 64 0) 128 ∧
      (∀ r, r ≠ .rsi → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm7 → ∀ l, t.lane r l = s.lane r l) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [counterHead, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc, readSrc32, State.load128, State.load32, State.setReg32,
    ea_at, BitVec.ofInt_natCast, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
    State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr,
    reduceCtorEq, ↓reduceIte, hc, hl, Option.map_some, setWidth_setWidth_32,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.lane, xmm_setReg, xmm_setV, ite_true]
  · intro r h1 h2
    simp only [h1, h2, ite_false]
  · intro r hr l
    simp only [State.lane, xmm_setReg, ymmHi_setReg, xmm_setV, ymmHi_setV_128, hr, ite_false]
  · trivial
  · trivial
  · trivial

end VG.Proof.Gcm.X86_64.StitchAvx8
