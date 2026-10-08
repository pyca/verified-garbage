import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# Integer preparation of the counter and hash buffers

The integer pipeline writes counter words and reversed hash inputs while
leaving every vector register available to the interleaved AES/GHASH work.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter prepare)

private theorem ea_at (s : State) (r : Reg) (n : Nat) :
    s.ea (at_ r n) = s.gpr r + BitVec.ofNat 64 n := by
  simp [at_, State.ea, BitVec.ofInt_natCast]

private theorem store32_eq (s : State) (a : Addr) (v : BitVec 32) :
    s.store32 a v = if InRegions s.wr a 4 then some (s.setMem (s.mem.writeW a v)) else none := rfl

private theorem store64_eq (s : State) (a : Addr) (v : BitVec 64) :
    s.store64 a v = if InRegions s.wr a 8 then some (s.setMem (s.mem.writeW a v)) else none := rfl

/-- Integer preparation only changes `rax`, flags, and memory. -/
structure BufferFrame (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  xmm : t.xmm = s.xmm
  ymmHi : t.ymmHi = s.ymmHi
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem BufferFrame.refl (s : State) : BufferFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem BufferFrame.trans {s t u : State} (h : BufferFrame s t) (h' : BufferFrame t u) :
    BufferFrame s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.xmm.trans h.xmm,
    h'.ymmHi.trans h.ymmHi, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem BufferFrame.lane {s t : State} (h : BufferFrame s t) (r : XReg) (l : Nat) :
    t.lane r l = s.lane r l := by
  simp only [State.lane, h.xmm, h.ymmHi]

theorem prepCounter_ok (s : State) (i : Nat)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (652 + 16 * i)) 4) :
    WP isa (.block (prepCounter i)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (652 + 16 * i))
        (bswap32 ((s.gpr .r8).setWidth 32 + BitVec.ofNat 32 i)) ∧ BufferFrame s t := by
  apply WP.of_runBlock
  simp only [prepCounter, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc32, execAlu32, State.setReg32, gpr_setReg, gpr_arithFlags,
    reduceCtorEq, ↓reduceIte, Option.map_some, Option.bind_some,
    setWidth_setWidth_32, store32_eq, ea_at, wr_setReg, wr_arithFlags,
    mem_setReg, mem_arithFlags, hw, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [State.setMem_gpr, gpr_setReg, gpr_arithFlags, hr, ite_false]
  · simp only [State.setMem_xmm, xmm_setReg, xmm_arithFlags]
  · simp only [State.setMem_ymmHi, ymmHi_setReg, ymmHi_arithFlags]
  · simp only [State.setMem_rd, rd_setReg, rd_arithFlags]
  · simp only [State.setMem_wr, wr_setReg, wr_arithFlags]

/-- The high source word is stored first, as the low native field word. -/
def prepareMem (m : Mem) (src dst : Addr) : Mem :=
  (m.writeW dst (bswap64 (m.readW (src + 8) 64))).writeW (dst + 8)
    (bswap64 (m.readW src 64))

theorem prepare_ok (s : State) (k : Nat)
    (hr₀ : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) 8)
    (hr₁ : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * k + 8)) 8)
    (hw₀ : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (512 + 16 * (k % 8))) 8)
    (hw₁ : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (520 + 16 * (k % 8))) 8)
    (hsep : Mem.Sep (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) 8
      (s.gpr .r11 + BitVec.ofNat 64 (512 + 16 * (k % 8))) 8) :
    WP isa (.block (prepare k)) s fun t =>
      t.mem = prepareMem s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * k))
        (s.gpr .r11 + BitVec.ofNat 64 (512 + 16 * (k % 8))) ∧ BufferFrame s t := by
  apply WP.of_runBlock
  simp only [prepare, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc, State.load64, store64_eq, ea_at, gpr_setReg, mem_setReg,
    rd_setReg, wr_setReg, State.setMem_gpr, State.setMem_rd, State.setMem_wr,
    State.setMem_mem, reduceCtorEq, ↓reduceIte, hr₀, hr₁, hw₀, hw₁,
    Option.map_some, Mem.readW_writeW_sep (w := 64) (w' := 64) hsep (by decide),
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · have es : s.gpr .rdx + BitVec.ofNat 64 (16 * k) + 8 =
        s.gpr .rdx + BitVec.ofNat 64 (16 * k + 8) := by
      rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    have ed : s.gpr .r11 + BitVec.ofNat 64 (512 + 16 * (k % 8)) + 8 =
        s.gpr .r11 + BitVec.ofNat 64 (520 + 16 * (k % 8)) := by
      rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    simp only [prepareMem, es, ed]
  · constructor
    · intro r hr
      simp only [State.setMem_gpr, gpr_setReg, hr, ite_false]
    · simp only [State.setMem_xmm, xmm_setReg]
    · simp only [State.setMem_ymmHi, ymmHi_setReg]
    · simp only [State.setMem_rd, rd_setReg]
    · simp only [State.setMem_wr, wr_setReg]

private theorem read128_halves (m : Mem) (a : Addr) :
    m.readW a 128 = m.readW (a + 8) 64 ++ m.readW a 64 := by
  have h := BitVec.extractLsb'_append_extractLsb' (x := m.readW a 128) (w := 64) (len := 64)
  rw [readW_extract m a (k := 8) (n := 8) (by decide),
    readW_extract m a (k := 0) (n := 8) (by decide)] at h
  simpa using h.symm

/-- A prepared pair of integer stores is the native representation of the
big-endian GHASH block. -/
theorem prepareMem_read (m : Mem) (src dst : Addr) :
    (prepareMem m src dst).readW dst 128 = Spec.Gcm.blockAt m src := by
  rw [read128_halves, prepareMem, Mem.readW_writeW_self64]
  have hs : Mem.Sep dst 8 (dst + 8) 8 := by
    simpa using
      (Offset.sep dst (d := 0) (e := 8) (n := 8) (k := 8) (by omega) (by omega) (by omega))
  rw [Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64]
  simpa using blockAt_bswap m src

theorem prepareMem_frame (m : Mem) (src dst : Addr) :
    Frame [⟨dst, 16⟩] m (prepareMem m src dst) := by
  unfold prepareMem
  refine ((Frame.refl _ _).writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  · exact Offset.contains_base dst (d := 8) (n := 8) (k := 16) (by decide) (by decide)

/-- The memory effect of preparing any collection of next-counter slots. -/
def prepCountersMem (m : Mem) (p : Addr) (v : BitVec 32) (is : List Nat) : Mem :=
  is.foldl (fun m i => m.writeW (p + BitVec.ofNat 64 (652 + 16 * i))
    (bswap32 (v + BitVec.ofNat 32 i))) m

theorem prepCounters_ok (is : List Nat) (s : State)
    (hw : ∀ i ∈ is, InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (652 + 16 * i)) 4) :
    WP isa (.block (is.flatMap prepCounter)) s fun t =>
      t.mem = prepCountersMem s.mem (s.gpr .r11) ((s.gpr .r8).setWidth 32) is ∧ BufferFrame s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, BufferFrame.refl _⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (prepCounter_ok s i (hw i List.mem_cons_self)) fun t ⟨hm, hf⟩ => ?_
    refine WP.mono (ih t (fun j hj => by
      rw [hf.wr, hf.gpr .r11 (by decide)]
      exact hw j (List.mem_cons_of_mem _ hj))) fun u ⟨hm', hf'⟩ => ⟨?_, hf.trans hf'⟩
    rw [hm', hf.gpr .r11 (by decide), hf.gpr .r8 (by decide), hm]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8
