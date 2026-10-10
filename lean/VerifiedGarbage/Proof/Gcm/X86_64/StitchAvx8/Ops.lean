import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffers
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base

/-! ## Env -/
section

/-!
# The part of the eight-state loop preserved by its scratch preparation

The hash inputs and counter templates occupy bytes 512–767. The powers,
constants and saved entry registers lie outside that range. Keeping their
frame separate lets both integer preparation and AES rounds preserve them.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64 (revMask)

def workR (s₀ : State) : Region := ⟨pp s₀ + 512, 256⟩

/-- The memory and pointers that every complete batch preserves. -/
structure Env (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = cp s₀
  rcx : s.gpr .rcx = yp s₀
  r11 : s.gpr .r11 = pp s₀
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  other : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .rsi →
    s.gpr r = s₀.gpr r
  frame : Frame [dR s₀, pR s₀] s₀.mem s.mem
  powers : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 = P k
  mask : s.mem.readW (pp s₀ + 768) 128 = revMask
  poly : s.mem.readW (pp s₀ + 784) 128 = poly
  rounds : s.mem.readW (pp s₀ + 800) 64 = s₀.gpr .rsi
  data : s.mem.readW (pp s₀ + 808) 64 = dp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Env.keys {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (h : Env s₀ P s) :
    VG.Proof.Aes.X86_64.AesNi.Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [h.rdi, sch_frame hp h.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [h.rd, h.wr, h.rdi]
      exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem Env.yframe {s₀ s t : State} {P : Nat → Block} {rs : List XReg}
    (h : Env s₀ P s) (f : YFrame rs s t) : Env s₀ P t := by
  constructor
  · rw [f.gpr]; exact h.rdi
  · rw [f.gpr]; exact h.rsi
  · rw [f.gpr]; exact h.rcx
  · rw [f.gpr]; exact h.r11
  · rw [f.gpr]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [f.gpr]; exact h.other r h1 h2 h3 h4 h5 h6
  · rw [f.mem]; exact h.frame
  · intro k hk; rw [f.mem]; exact h.powers k hk
  · rw [f.mem]; exact h.mask
  · rw [f.mem]; exact h.poly
  · rw [f.mem]; exact h.rounds
  · rw [f.mem]; exact h.data
  · exact f.rd.trans h.rd
  · exact f.wr.trans h.wr

/-- A scratch write preserves reads outside the two changing buffers. -/
theorem work_read {s₀ : State} {m m' : Mem} (h : Frame [workR s₀] m m')
    (d n : Nat) (hd : d + n ≤ 512 ∨ 768 ≤ d) (hn : d + n ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) =
      m.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) := by
  apply h.readW (r := ⟨pp s₀ + BitVec.ofNat 64 d, n⟩)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint (pp s₀) hd (by omega) (by decide)
  · omega

theorem Env.buffer {s₀ s t : State} {P : Nat → Block}
    (h : Env s₀ P s) (f : BufferFrame s t) (hm : Frame [workR s₀] s.mem t.mem) :
    Env s₀ P t := by
  constructor
  · rw [f.gpr _ (by decide)]; exact h.rdi
  · rw [f.gpr _ (by decide)]; exact h.rsi
  · rw [f.gpr _ (by decide)]; exact h.rcx
  · rw [f.gpr _ (by decide)]; exact h.r11
  · rw [f.gpr _ (by decide)]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [f.gpr r h1]; exact h.other r h1 h2 h3 h4 h5 h6
  · refine h.frame.trans (hm.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨pR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · intro k hk
    rw [work_read hm (128 + 16 * k) 16 (by omega) (by omega)]
    exact h.powers k hk
  · exact (work_read hm 768 16 (by omega) (by omega)).trans h.mask
  · exact (work_read hm 784 16 (by omega) (by omega)).trans h.poly
  · exact (work_read hm 800 8 (by omega) (by omega)).trans h.rounds
  · exact (work_read hm 808 8 (by omega) (by omega)).trans h.data
  · exact f.rd.trans h.rd
  · exact f.wr.trans h.wr

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## FinishOps -/
section

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

end

/-! ## SetupOps -/
section

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

end

/-! ## Metadata -/
section

/-! # Scratch metadata saved at entry and restored at exit -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64

def metaR (s : State) : Region := ⟨s.gpr .r11 + BitVec.ofNat 64 768, 48⟩

theorem meta_frame (s : State) : Frame [metaR s] s.mem (metaMem s) := by
  unfold metaMem
  refine (((Frame.refl _ _).writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ ?_).writeW
    List.mem_cons_self _ ?_ |>.writeW List.mem_cons_self _ ?_
  · exact Offset.contains (s.gpr .r11) (d := 768) (n := 16) (e := 768) (k := 48) (by decide) (by decide) (by decide)
  · exact Offset.contains (s.gpr .r11) (d := 784) (n := 16) (e := 768) (k := 48) (by decide) (by decide) (by decide)
  · exact Offset.contains (s.gpr .r11) (d := 808) (n := 8) (e := 768) (k := 48) (by decide) (by decide) (by decide)
  · exact Offset.contains (s.gpr .r11) (d := 800) (n := 8) (e := 768) (k := 48) (by decide) (by decide) (by decide)

theorem meta_mask (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 768) 128 = s.lane .xmm0 0 := by
  rw [metaMem,
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 768) (n := 16) (e := 800) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 768) (n := 16) (e := 808) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 768) (n := 16) (e := 784) (k := 16) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self s.mem _ 16 _ (by decide)]

theorem meta_poly (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 784) 128 = s.lane .xmm1 0 := by
  rw [metaMem,
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 784) (n := 16) (e := 800) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 784) (n := 16) (e := 808) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self _ _ 16 _ (by decide)]

theorem meta_rounds (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 800) 64 = s.gpr .rsi := by
  rw [metaMem, Mem.readW_writeW_self64]

theorem meta_data (s : State) :
    (metaMem s).readW (s.gpr .r11 + BitVec.ofNat 64 808) 64 = s.gpr .rdx := by
  rw [metaMem,
    Mem.readW_writeW_sep (Offset.sep (s.gpr .r11) (d := 808) (n := 8) (e := 800) (k := 8) (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64]

end VG.Proof.Gcm.X86_64.StitchAvx8

end
