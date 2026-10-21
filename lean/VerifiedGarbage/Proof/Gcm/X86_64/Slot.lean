module

public import VerifiedGarbage.Impl.Gcm.X86_64.Slot
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.ZVecKeep
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Gcm.X86_64.Counter
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock
public import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev

/-!
# AES-GCM's counter blocks in memory

`Impl.Gcm.X86_64.Slot`'s code, for working space at `p` (in `r11`): the
sixteen blocks at `p + slot` are counter blocks of `C` (`SlotOk`), and `r10d`
holds the 32 bits `inc₃₂` increments of the first. `put_ok`: one block's
last four bytes written from `r10d`, which advances. `restoreK_ok`: `r10` the
address of the last round key again.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Slot

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Gcm.X86_64.Slot (slot put puts refill loads ctrsM copies init restoreK)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Spec.Gcm (Block blockAt inc32)

theorem bswap32_bswap32 (x : BitVec 32) : bswap32 (bswap32 x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_bswap32]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, decide_eq_true, Bool.true_and] <;>
  exact congrArg _ (by omega)

private theorem ea_at (s : State) (r : Reg) (n : Nat) :
    s.ea (at_ r n) = s.gpr r + BitVec.ofNat 64 n := by
  simp [at_, State.ea, BitVec.ofInt_natCast]

private theorem store32_eq (s : State) (a : Addr) (v : BitVec 32) :
    s.store32 a v = if InRegions s.wr a 4 then some (s.setMem (s.mem.writeW a v)) else none := rfl

/-- Scalar code that keeps everything but `r10`, the flags and memory. -/
structure CFrame (s t : State) : Prop where
  gpr : ∀ r, r ≠ .r10 → t.gpr r = s.gpr r
  xmm : t.xmm = s.xmm
  ymmHi : t.ymmHi = s.ymmHi
  zmmHi : t.zmmHi = s.zmmHi
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem CFrame.refl (s : State) : CFrame s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CFrame.trans {s t u : State} (h : CFrame s t) (h' : CFrame t u) : CFrame s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.xmm.trans h.xmm, h'.ymmHi.trans h.ymmHi,
    h'.zmmHi.trans h.zmmHi, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem CFrame.zlane {s t : State} (h : CFrame s t) (r : XReg) (l : Nat) : t.zlane r l = s.zlane r l := by
  simp only [State.zlane, State.lane, h.xmm, h.ymmHi, h.zmmHi]

/-- One block's last four bytes, at `r11 + slot + 16 i + 12`, from `r10d`
byte-reversed; `r10d` advanced. -/
theorem put_ok (s : State) (i : Nat)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12)) 4) :
    WP isa (.block (put i)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12))
        (bswap32 ((s.gpr .r10).setWidth 32)) ∧
      (t.gpr .r10).setWidth 32 = (s.gpr .r10).setWidth 32 + 1 ∧ CFrame s t := by
  suffices h : WP isa (.block (put i)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12))
        (bswap32 ((s.gpr .r10).setWidth 32)) ∧
      (t.gpr .r10).setWidth 32 = (s.gpr .r10).setWidth 32 + 1 ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr from
    WP.mono (WP.zvecKeep (c := .block (put i)) (by rfl) h) fun t ⟨⟨hm, hc, hg, hrd, hwr⟩, hx, hy, hz⟩ =>
      ⟨hm, hc, ⟨hg, hx, hy, hz, hrd, hwr⟩⟩
  apply WP.of_runBlock
  simp only [put, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc32, execAlu32, State.setReg32, gpr_setReg, gpr_arithFlags,
    reduceCtorEq, ↓reduceIte, Option.bind_some,
    setWidth_setWidth_32, store32_eq, ea_at, wr_setReg, wr_arithFlags,
    mem_setReg, mem_arithFlags, hw, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp only [State.setMem_gpr, gpr_setReg, ↓reduceIte, setWidth_setWidth_32, bswap32_bswap32]
  · intro r hr
    simp only [State.setMem_gpr, gpr_setReg, hr, ite_false]
  · simp only [State.setMem_rd, rd_setReg, rd_arithFlags]
  · simp only [State.setMem_wr, wr_setReg]

/-- The memory after `puts n` from `r10d = v`, with the working space at `p`. -/
def putsMem (m : Mem) (p : Addr) (v : BitVec 32) : Nat → Mem
  | 0 => m
  | n + 1 => (putsMem m p v n).writeW (p + BitVec.ofNat 64 (slot + 16 * n + 12)) (bswap32 (v + BitVec.ofNat 32 n))

theorem puts_ok (n : Nat) (s : State)
    (hw : ∀ i < n, InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12)) 4) :
    WP isa (.block (puts n)) s fun t =>
      t.mem = putsMem s.mem (s.gpr .r11) ((s.gpr .r10).setWidth 32) n ∧
      (t.gpr .r10).setWidth 32 = (s.gpr .r10).setWidth 32 + BitVec.ofNat 32 n ∧ CFrame s t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, by simp, CFrame.refl _⟩
  | succ n ih =>
    rw [puts, WP.block_append_iff]
    refine WP.mono (ih fun i hi => hw i (by omega)) fun t ⟨hm, hc, hf⟩ => ?_
    refine WP.mono (put_ok t n (by rw [hf.wr, hf.gpr .r11 (by decide)]; exact hw n (by omega)))
      fun u ⟨hm', hc', hf'⟩ => ⟨?_, ?_, hf.trans hf'⟩
    · rw [hm', hm, hc, hf.gpr .r11 (by decide)]; rfl
    · rw [hc', hc, BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- The sixteen blocks of the slot, for working space at `p`: block `i` is
`inc₃₂^(f i)(C)`. -/
def SlotOk (p : Addr) (C : Block) (f : Nat → Nat) (m : Mem) : Prop :=
  ∀ i < 16, blockAt m (p + BitVec.ofNat 64 (slot + 16 * i)) = Nat.repeat inc32 (f i) C

/-- The slot, for working space at `p`. -/
abbrev slotR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 slot, 256⟩

/-- `puts n` from `r10d = lo(C) + t` makes blocks `i < n` `inc₃₂^(t + i)(C)`,
if they were counter blocks of `C` no further than that. -/
theorem putsMem_ok {p : Addr} {C : Block} {f : Nat → Nat} {m : Mem} {t : Nat} :
    ∀ n, n ≤ 16 → SlotOk p C f m → (∀ i < n, f i ≤ t + i) →
      SlotOk p C (fun i => if i < n then t + i else f i)
        (putsMem m p (C.extractLsb' 0 32 + BitVec.ofNat 32 t) n)
  | 0, _, h, _ => fun i hi => by simpa [putsMem] using h i hi
  | n + 1, hn, h, hf => by
    have ih := putsMem_ok n (by omega) h (fun i hi => hf i (by omega))
    intro i hi
    simp only [putsMem]
    by_cases he : i = n
    · subst i
      have hb := ih n hi
      simp only [Nat.lt_irrefl, ite_false] at hb
      have e := refreshCounter_ok _ _ C (f n) (t + n - f n) hb
      rw [Offset.add_add, show f n + (t + n - f n) = t + n by have := hf n (by omega); omega] at e
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show slot + 16 * n + 12 = slot + 16 * n + 12 from rfl]
      simpa only [Nat.lt_add_one, ite_true] using e
    · rw [VG.Proof.Aes.X86_64.Vaes.blockAt_writeW_sep _ _ (Offset.sep p (by
          simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot]; omega))]
      have hb := ih i hi
      simp only [show (i < n + 1) = (i < n) from propext ⟨fun h => by omega, fun h => by omega⟩]
      exact hb

/-- The slot is kept by writes apart from it. -/
theorem SlotOk.frame {p : Addr} {C : Block} {f : Nat → Nat} {m m' : Mem} (h : SlotOk p C f m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotR p).Disjoint r) : SlotOk p C f m' := by
  intro i hi
  rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf fun r hr => (hd r hr).sub_left (by
    rw [show slot + 16 * i = slot + 16 * i from rfl, ← Offset.add_add]
    exact Offset.sub_base _ (by omega))]
  exact h i hi

/-- `puts n` writes only the slot. -/
theorem putsMem_frame (m : Mem) (p : Addr) (v : BitVec 32) : ∀ n, n ≤ 16 → Frame [slotR p] m (putsMem m p v n)
  | 0, _ => Frame.refl _ _
  | n + 1, hn => (putsMem_frame m p v n (by omega)).writeW List.mem_cons_self _ (by
      rw [show slot + 16 * n + 12 = slot + (16 * n + 12) by omega, ← Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega))

/-- The address of the last round key, from `rdi` and the round count in `rsi`. -/
abbrev kAddr (s : State) : Addr := s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat)

theorem kAddr_of {s t : State} (h : CFrame s t) : kAddr t = kAddr s := by
  simp only [kAddr, h.gpr .rdi (by decide), h.gpr .rsi (by decide)]

/-- `restoreK`: `r10 = rdi + 16 rsi`. -/
theorem restoreK_ok (s : State) :
    WP isa (.block restoreK) s fun t => t.gpr .r10 = kAddr s ∧ t.mem = s.mem ∧ CFrame s t := by
  suffices h : WP isa (.block restoreK) s fun t =>
      t.gpr .r10 = kAddr s ∧ t.mem = s.mem ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr from
    WP.mono (WP.zvecKeep (c := .block _) (by rfl) h) fun t ⟨⟨hc, hm, hg, hrd, hwr⟩, hx, hy, hz⟩ =>
      ⟨hc, hm, ⟨hg, hx, hy, hz, hrd, hwr⟩⟩
  apply WP.of_runBlock
  simp only [restoreK, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
    wr_setReg, wr_arithFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', and_true]
  refine ⟨?_, trivial, fun x hx => by simp only [hx, ite_false]⟩
  simp only [kAddr]
  bv_omega

/-- `r10d` the counter of the block at `r11 + slot`, advanced by `d`. -/
theorem ctrHead_ok (d : Nat) (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 4) :
    WP isa (.block [.mov32 .r10 (.mem (at_ .r11 (slot + 12))), .bswap32 .r10,
        .alu32 .add .r10 (.imm (BitVec.ofNat 32 d))]) s fun t =>
      (t.gpr .r10).setWidth 32 =
        bswap32 (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 32) + BitVec.ofNat 32 d ∧
      t.mem = s.mem ∧ CFrame s t := by
  suffices h : WP isa (.block [.mov32 .r10 (.mem (at_ .r11 (slot + 12))), .bswap32 .r10,
      .alu32 .add .r10 (.imm (BitVec.ofNat 32 d))]) s fun t =>
      (t.gpr .r10).setWidth 32 =
        bswap32 (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 32) + BitVec.ofNat 32 d ∧
      t.mem = s.mem ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr from
    WP.mono (WP.zvecKeep (c := .block _) (by rfl) h) fun t ⟨⟨hc, hm, hg, hrd, hwr⟩, hx, hy, hz⟩ =>
      ⟨hc, hm, ⟨hg, hx, hy, hz, hrd, hwr⟩⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, readSrc32, State.load32, ea_at, hr,
    Option.map_some, execAlu32, Option.bind_some, State.setReg32, gpr_setReg, gpr_arithFlags,
    ↓reduceIte, setWidth_setWidth_32, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
    wr_setReg, wr_arithFlags, Option.some.injEq, exists_eq_left', true_and, and_true]
  exact fun x hx => by simp only [hx, ite_false]

/-- The counter of the slot's first block. -/
theorem slot_ctr {p : Addr} {C : Block} {c : Nat} {m : Mem} (h : SlotOk p C (fun i => c + i) m) :
    bswap32 (m.readW (p + BitVec.ofNat 64 (slot + 12)) 32) = C.extractLsb' 0 32 + BitVec.ofNat 32 c := by
  rw [← Offset.add_add, VG.Proof.Aes.X86_64.icb_lo, show slot = slot + 16 * 0 from rfl, h 0 (by decide),
    VG.Proof.Aes.repeat_inc32_lo]
  rfl

/-- `refill d`: the slot advanced by `d` blocks; `r10` the address of the
last round key. -/
theorem refill_ok (d : Nat) (s : State) {C : Block} {c : Nat}
    (hS : SlotOk (s.gpr .r11) C (fun i => c + i) s.mem)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 slot) 256) :
    WP isa (.block (refill d)) s fun t =>
      SlotOk (s.gpr .r11) C (fun i => c + d + i) t.mem ∧ t.gpr .r10 = kAddr s ∧
      Frame [slotR (s.gpr .r11)] s.mem t.mem ∧ CFrame s t := by
  have hw' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 slot) 256 :=
    VG.Proof.Aes.X86_64.AesNi.inRegions_wr hw
  rw [refill, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ctrHead_ok d s (by
    rw [← Offset.add_add]; exact VG.Proof.Gcm.X86_64.Stitch.in_sub hw' (by decide))) fun t ⟨hc₁, hm₁, hf₁⟩ => ?_
  have hp : t.gpr .r11 = s.gpr .r11 := hf₁.gpr .r11 (by decide)
  have hw₁ : ∀ i < 16, InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12)) 4 := fun i hi => by
    rw [hf₁.wr, hp, show slot + 16 * i + 12 = slot + (16 * i + 12) by omega, ← Offset.add_add]
    exact VG.Proof.Gcm.X86_64.Stitch.in_sub hw (by omega)
  refine WP.mono (puts_ok 16 t hw₁) fun u ⟨hm₂, hc₂, hf₂⟩ => ?_
  refine WP.mono (restoreK_ok u) fun w ⟨hc₃, hm₃, hf₃⟩ => ?_
  have hv : (t.gpr .r10).setWidth 32 = C.extractLsb' 0 32 + BitVec.ofNat 32 (c + d) := by
    rw [hc₁, slot_ctr hS, BitVec.add_assoc, BitVec.ofNat_add]
  have hfm : Frame [slotR (s.gpr .r11)] s.mem u.mem := by
    rw [hm₂, hp, hm₁]; exact putsMem_frame _ _ _ 16 (Nat.le_refl _)
  refine ⟨?_, by rw [hc₃, kAddr_of hf₂, kAddr_of hf₁], by rw [hm₃]; exact hfm, (hf₁.trans hf₂).trans hf₃⟩
  rw [hm₃, hm₂, hp, hv]
  have := putsMem_ok (p := s.gpr .r11) (C := C) (f := fun i => c + i) (m := t.mem) (t := c + d) 16
    (Nat.le_refl _) (by rw [hm₁]; exact hS) (fun i _ => by omega)
  intro i hi
  simpa only [hi, ite_true] using this i hi

/-- One register's four blocks loaded from `r11 + d`. -/
theorem load1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 d) 64) :
    WP isa (.block [.vmovdqu32Load b (at_ .r11 d)]) s fun t =>
      (∀ l < 4, t.zlane b l = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128) ∧
      ZFrame [b] s t := by
  let v := s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 d) 512
  rw [WP.block_cons_iff]
  refine ⟨s.setZ b (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128),
    by simp only [isa, exec, State.load512, ea_at, hin, ite_true, Option.map_some]; rfl,
    WP.block_nil ⟨fun l hl => ?_, ⟨rfl, rfl, rfl, rfl, fun r hr l hl => ?_⟩⟩⟩
  · rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl]
    exact VG.Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl
  · exact State.zlane_setZ_ne _ (by simpa using hr) _ _ _ _ hl

/-- The lanes of a load from the slot, from its blocks. -/
theorem slot_lane {p : Addr} {C : Block} {f : Nat → Nat} {m : Mem} (h : SlotOk p C f m) {k l : Nat}
    (hk : k < 4) (hl : l < 4) :
    m.readW (p + BitVec.ofNat 64 (slot + 64 * k) + BitVec.ofNat 64 (16 * l)) 128 =
      XBinOp.eval .pshufb (Nat.repeat inc32 (f (4 * k + l)) C) revMask := by
  rw [Offset.add_add, show slot + 64 * k + 16 * l = slot + 16 * (4 * k + l) by omega,
    ← h _ (by omega), VG.Proof.Gcm.X86_64.blockAt_eq, VG.Proof.Gcm.X86_64.pshufb_rev_rev]

/-- `loads rs k`: register `j` of `rs` gets the slot's blocks `4 (k + j)` …. -/
theorem loads_ok {C : Block} {f : Nat → Nat} : ∀ (rs : List XReg) (k : Nat) (s : State),
    SlotOk (s.gpr .r11) C f s.mem → k + rs.length ≤ 4 → rs.Nodup →
    InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 slot) 256 →
    WP isa (.block (loads rs k)) s fun t =>
      (∀ j (h : j < rs.length), ∀ l < 4,
        t.zlane rs[j] l = XBinOp.eval .pshufb (Nat.repeat inc32 (f (4 * (k + j) + l)) C) revMask) ∧
      ZFrame rs s t
  | [], _, s, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), ZFrame.refl _ _⟩
  | b :: bs, k, s, hS, hk, hnd, hin => by
    simp only [List.length_cons] at hk
    rw [loads, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (load1_ok b (slot + 64 * k) s (by
      rw [show slot + 64 * k = slot + 64 * k from rfl, ← Offset.add_add]
      exact VG.Proof.Gcm.X86_64.Stitch.in_sub hin (by omega))) fun t ⟨hb, hf⟩ => ?_
    have hS' : SlotOk (t.gpr .r11) C f t.mem := by rw [hf.gpr, hf.mem]; exact hS
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    refine WP.mono (loads_ok bs (k + 1) t hS' (by omega) (List.nodup_cons.mp hnd).2
      (by rw [hf.rd, hf.wr, hf.gpr]; exact hin)) fun u ⟨hu, hf'⟩ => ⟨fun j hj l hl => ?_, ?_⟩
    · cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf'.zlane _ hbs l hl, hb l hl]
        exact slot_lane hS (by omega) hl
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [hu j (by simpa using hj) l hl, show k + 1 + j = k + (j + 1) by omega]
    · refine (hf.comp hf').mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h <;> simp [h]

/-- `ctrsM rs`: the registers `rs` get the group's counter blocks, lane `l`
of register `k` block `4 k + l` (as `VaesZ.ctrsZ_ok`), and the slot advances
to the next group; `r10`, the address of the last round key, is computed
again. -/
theorem ctrsM_ok (rs : List XReg) (s : State) {C : Block} {c : Nat}
    (hS : SlotOk (s.gpr .r11) C (fun i => c + i) s.mem) (h10 : s.gpr .r10 = kAddr s)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 slot) 256)
    (hk : rs.length ≤ 4) (hnd : rs.Nodup) :
    WP isa (.block (ctrsM rs)) s fun t =>
      (∀ k (h : k < rs.length), ∀ l < 4,
        t.zlane rs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) C) revMask) ∧
      SlotOk (s.gpr .r11) C (fun i => c + 4 * rs.length + i) t.mem ∧
      Frame [slotR (s.gpr .r11)] s.mem t.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r, r ∉ rs → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  rw [ctrsM, WP.block_append_iff]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 slot) 256 :=
    VG.Proof.Aes.X86_64.AesNi.inRegions_wr hw
  refine WP.mono (loads_ok rs 0 s hS (by omega) hnd hin) fun t ⟨hL, hf⟩ => ?_
  refine WP.mono (refill_ok (4 * rs.length) t (C := C) (c := c) (by rw [hf.gpr, hf.mem]; exact hS)
    (by rw [hf.gpr, hf.wr]; exact hw)) fun u ⟨hS', hc', hm', hf'⟩ => ?_
  rw [hf.gpr] at hS' hm'
  refine ⟨fun k hk l hl => ?_, hS', by rw [← hf.mem]; exact hm', ?_, by rw [hf'.rd, hf.rd], by rw [hf'.wr, hf.wr],
    fun r hr l hl => by rw [hf'.zlane, hf.zlane r hr l hl]⟩
  · rw [hf'.zlane, hL k hk l hl, show 4 * (0 + k) + l = 4 * k + l by omega, Nat.add_assoc]
  · funext r
    by_cases h : r = .r10
    · subst h; rw [hc', h10]; simp only [kAddr, hf.gpr]
    · rw [hf'.gpr r h, hf.gpr]

/-! ## The first group -/

/-- `vbroadcasti32x4 zmm13, [rax]`. -/
theorem bcast_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax) 16) :
    WP isa (.block [.vbroadcasti32x4 .xmm13 (at_ .rax 0)]) s fun t =>
      (∀ l < 4, t.zlane .xmm13 l = s.mem.readW (s.gpr .rax) 128) ∧ ZFrame [.xmm13] s t := by
  let v := s.mem.readW (s.gpr .rax) 128
  rw [WP.block_cons_iff]
  refine ⟨s.setZ .xmm13 v v v v, by
      simp only [isa, exec, State.load128, ea_at, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hr, ite_true,
        Option.map_some]; rfl,
    WP.block_nil ⟨fun l hl => ?_, ⟨rfl, rfl, rfl, rfl, fun r hr' l hl => ?_⟩⟩⟩
  · rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun _ => v) hl]
  · exact State.zlane_setZ_ne _ (by simpa using hr') _ _ _ _ hl

/-- `copies n`: four copies of the block `V` in `zmm13` stored over the
first `n` fours of the slot. -/
theorem copies_ok {V : BitVec 128} : ∀ (n : Nat) (s : State), n ≤ 4 →
    (∀ l < 4, s.zlane .xmm13 l = V) → InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 slot) 256 →
    WP isa (.block (copies n)) s fun t =>
      (∀ i < 4 * n, blockAt t.mem (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i)) =
        XBinOp.eval .pshufb V revMask) ∧
      Frame [slotR (s.gpr .r11)] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r l, t.zlane r l = s.zlane r l)
  | 0, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | n + 1, s, hn, hV, hw => by
    rw [copies, WP.block_append_iff]
    refine WP.mono (copies_ok n s (by omega) hV hw) fun t ⟨hb, hf, hg, hrd, hwr, hz⟩ => ?_
    have hin : InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 (slot + 64 * n)) 64 := by
      rw [hwr, hg, ← Offset.add_add]
      exact VG.Proof.Gcm.X86_64.Stitch.in_sub hw (by omega)
    rw [WP.block_cons_iff]
    refine ⟨t.setMem (t.mem.writeW (t.gpr .r11 + BitVec.ofNat 64 (slot + 64 * n)) (t.zmm .xmm13)), by
      simp only [isa, exec, State.store512_eq, ea_at, hin, ite_true], WP.block_nil ?_⟩
    simp only [State.setMem_mem, State.setMem_gpr, State.setMem_rd, State.setMem_wr]
    refine ⟨fun i hi => ?_, ?_, hg, hrd, hwr, fun r l => by rw [← hz r l]; rfl⟩
    · rw [hg]
      by_cases hi' : i < 4 * n
      · rw [VG.Proof.Aes.X86_64.Vaes.blockAt_writeW_sep _ _ (Offset.sep _ (by simp only [slot]; omega)
          (by simp only [slot]; omega) (by simp only [slot]; omega))]
        exact hb i hi'
      · obtain ⟨l, hl, rfl⟩ : ∃ l, l < 4 ∧ i = 4 * n + l := ⟨i - 4 * n, by omega, by omega⟩
        rw [show s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * (4 * n + l)) =
            s.gpr .r11 + BitVec.ofNat 64 (slot + 64 * n) + BitVec.ofNat 64 (16 * l) by
              rw [Offset.add_add]; congr 2; omega,
          VG.Proof.Aes.X86_64.VaesZ.blockAt_writeW_lane _ _ _ hl, VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl,
          hz, hV l hl]
    · refine hf.trans ((Frame.refl _ _).writeW List.mem_cons_self _ ?_)
      rw [hg, show slot + 64 * n = slot + 64 * n from rfl, ← Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)

/-- `r10d` the counter of the block at `rax`. -/
theorem ctrInit_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 12) 4) :
    WP isa (.block [.mov32 .r10 (.mem (at_ .rax 12)), .bswap32 .r10]) s fun t =>
      (t.gpr .r10).setWidth 32 = bswap32 (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 12) 32) ∧
      t.mem = s.mem ∧ CFrame s t := by
  suffices h : WP isa (.block [.mov32 .r10 (.mem (at_ .rax 12)), .bswap32 .r10]) s fun t =>
      (t.gpr .r10).setWidth 32 = bswap32 (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 12) 32) ∧
      t.mem = s.mem ∧ (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr from
    WP.mono (WP.zvecKeep (c := .block _) (by rfl) h) fun t ⟨⟨hc, hm, hg, hrd, hwr⟩, hx, hy, hz⟩ =>
      ⟨hc, hm, ⟨hg, hx, hy, hz, hrd, hwr⟩⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, readSrc32, State.load32, ea_at, hr,
    Option.map_some, State.setReg32, gpr_setReg, ↓reduceIte, setWidth_setWidth_32, mem_setReg, rd_setReg,
    wr_setReg, Option.some.injEq, exists_eq_left', true_and, and_true]
  exact fun x hx => by simp only [hx, ite_false]

/-- `init`: the slot holds the first group's counter blocks, of the block
at `rax`; `r10`, the address of the last round key, is computed again. -/
theorem init_ok (s : State) (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 slot) 256)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax) 16)
    (hd : Region.Disjoint ⟨s.gpr .rax, 16⟩ (slotR (s.gpr .r11))) (h10 : s.gpr .r10 = kAddr s) :
    WP isa (.block init) s fun t =>
      SlotOk (s.gpr .r11) (blockAt s.mem (s.gpr .rax)) (fun i => 0 + i) t.mem ∧
      Frame [slotR (s.gpr .r11)] s.mem t.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r, r ≠ .xmm13 → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  let C := blockAt s.mem (s.gpr .rax)
  let p := s.gpr .r11
  rw [init, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bcast_ok s hr) fun t₁ ⟨hz₁, hf₁⟩ => ?_
  refine WP.mono (copies_ok 4 t₁ (by decide) hz₁ (by rw [hf₁.gpr, hf₁.wr]; exact hw))
    fun t₂ ⟨hb₂, hm₂, hg₂, hrd₂, hwr₂, hz₂⟩ => ?_
  simp only [hf₁.gpr, hf₁.mem] at hb₂ hm₂
  refine WP.mono (ctrInit_ok t₂
    (by rw [hrd₂, hwr₂, hf₁.rd, hf₁.wr, hg₂, hf₁.gpr]; exact VG.Proof.Gcm.X86_64.Stitch.in_sub hr (by decide)))
    fun t₃ ⟨hc₃, hm₃, hf₃⟩ => ?_
  have hp₃ : t₃.gpr .r11 = p := by rw [hf₃.gpr .r11 (by decide), hg₂, hf₁.gpr]
  -- The slot holds sixteen copies of `C`.
  have hS₃ : SlotOk p C (fun _ => 0) t₃.mem := fun i hi => by
    rw [hm₃, hb₂ i (by omega), ← VG.Proof.Gcm.X86_64.blockAt_eq]
    rfl
  -- The counter of `C`: the block at `rax` is not in the slot.
  have hc₃' : (t₃.gpr .r10).setWidth 32 = C.extractLsb' 0 32 + BitVec.ofNat 32 0 := by
    have e : t₂.mem.readW (s.gpr .rax + BitVec.ofNat 64 12) 32 = s.mem.readW (s.gpr .rax + BitVec.ofNat 64 12) 32 :=
      hm₂.readW (r := ⟨s.gpr .rax, 16⟩) (Offset.contains_base _ (by decide) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)
    rw [hc₃, hg₂, hf₁.gpr, e, VG.Proof.Aes.X86_64.icb_lo]
    simp <;> rfl
  have hw₃ : ∀ i < 16, InRegions t₃.wr (t₃.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12)) 4 := fun i hi => by
    rw [hf₃.wr, hwr₂, hf₁.wr, hp₃, show slot + 16 * i + 12 = slot + (16 * i + 12) by omega, ← Offset.add_add]
    exact VG.Proof.Gcm.X86_64.Stitch.in_sub hw (by omega)
  refine WP.mono (puts_ok 16 t₃ hw₃) fun t₄ ⟨hm₄, hc₄, hf₄⟩ => ?_
  refine WP.mono (restoreK_ok t₄) fun t₅ ⟨hc₅, hm₅, hf₅⟩ => ?_
  rw [hp₃, hc₃'] at hm₄
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr l hl => ?_⟩
  · have := putsMem_ok (p := p) (C := C) (f := fun _ => 0) (m := t₃.mem) (t := 0) 16 (Nat.le_refl _) hS₃
      (fun i _ => by omega)
    intro i hi
    rw [hm₅, hm₄]
    simpa only [hi, ite_true] using this i hi
  · have F₃ : Frame [slotR p] t₃.mem (putsMem t₃.mem p (C.extractLsb' 0 32 + BitVec.ofNat 32 0) 16) :=
      putsMem_frame _ _ _ 16 (Nat.le_refl _)
    have F₂ : Frame [slotR p] s.mem t₃.mem := hm₃ ▸ hm₂
    have X := F₂.trans F₃
    exact hm₅ ▸ hm₄ ▸ X
  · funext r
    by_cases h : r = .r10
    · subst h; rw [hc₅, kAddr_of hf₄, kAddr_of hf₃, h10]; simp only [kAddr, hg₂, hf₁.gpr]
    · rw [hf₅.gpr r h, hf₄.gpr r h, hf₃.gpr r h, hg₂, hf₁.gpr]
  · rw [hf₅.rd, hf₄.rd, hf₃.rd, hrd₂, hf₁.rd]
  · rw [hf₅.wr, hf₄.wr, hf₃.wr, hwr₂, hf₁.wr]
  · rw [hf₅.zlane, hf₄.zlane, hf₃.zlane, hz₂, hf₁.zlane r (by simpa using hr) l hl]

/-! ## The counter stored -/

private theorem store128_eq (s : State) (a : Addr) (v : BitVec 128) :
    s.store128 a v = if InRegions s.wr a 16 then some (s.setMem (s.mem.writeW a v)) else none := rfl

/-- `storeCtr`: the slot's first block (the counter of the group it holds)
stored to `rax`. -/
theorem storeCtr_ok (s : State) {C : Block} {c : Nat} (hS : SlotOk (s.gpr .r11) C (fun i => c + i) s.mem)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 slot) 16) (hw : InRegions s.wr (s.gpr .rax) 16) :
    WP isa (.block Impl.Gcm.X86_64.Slot.storeCtr) s fun t =>
      blockAt t.mem (s.gpr .rax) = Nat.repeat inc32 c C ∧
      t.mem = s.mem.writeW (s.gpr .rax) (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 slot) 128) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r, r ≠ .xmm13 → ∀ l, t.zlane r l = s.zlane r l) := by
  let v := s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 slot) 128
  rw [Impl.Gcm.X86_64.Slot.storeCtr, WP.block_cons_iff]
  refine ⟨s.setV .l128 .xmm13 v 0, by simp only [isa, exec, State.load128, ea_at, hr, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨(s.setV .l128 .xmm13 v 0).setMem (s.mem.writeW (s.gpr .rax) v), by
    simp only [isa, exec, store128_eq, ea_at]
    simp [State.setV, hw], WP.block_nil ?_⟩
  refine ⟨?_, rfl, rfl, rfl, rfl, fun r hr l => ?_⟩
  · simp only [State.setMem_mem]
    rw [copyCounter_ok]
    simpa using hS 0 (by decide)
  · exact State.zlane_setV_ne s .l128 hr v 0 l

/-- The last four bytes of the block at `rax`: the counter of the slot's
first block plus `r9d - 16`, through `r10d`. -/
theorem patch_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 4)
    (hw : InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 12) 4) :
    WP isa (.block [.mov32 .r10 (.mem (at_ .r11 (slot + 12))), .bswap32 .r10, .alu32 .add .r10 (.reg .r9),
        .alu32 .sub .r10 (.imm 16), .bswap32 .r10, .store32 (at_ .rax 12) .r10]) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rax + BitVec.ofNat 64 12)
        (bswap32 (bswap32 (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 32) + (s.gpr .r9).setWidth 32 -
          BitVec.signExtend 32 (16 : BitVec 32))) ∧
      CFrame s t := by
  suffices h : WP isa (.block [.mov32 .r10 (.mem (at_ .r11 (slot + 12))), .bswap32 .r10,
      .alu32 .add .r10 (.reg .r9), .alu32 .sub .r10 (.imm 16), .bswap32 .r10, .store32 (at_ .rax 12) .r10]) s
      fun t =>
      t.mem = s.mem.writeW (s.gpr .rax + BitVec.ofNat 64 12)
        (bswap32 (bswap32 (s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 32) + (s.gpr .r9).setWidth 32 -
          BitVec.signExtend 32 (16 : BitVec 32))) ∧
      (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr from
    WP.mono (WP.zvecKeep (c := .block _) (by rfl) h) fun t ⟨⟨hm, hg, hrd, hwr⟩, hx, hy, hz⟩ =>
      ⟨hm, ⟨hg, hx, hy, hz, hrd, hwr⟩⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, readSrc32, State.load32, execAlu32,
    State.setReg32, gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, Option.bind_some, Option.map_some,
    setWidth_setWidth_32, store32_eq, ea_at, hr, wr_setReg, wr_arithFlags, mem_setReg,
    mem_arithFlags, Option.some.injEq, exists_eq_left', hw]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x hx
    simp only [State.setMem_gpr, gpr_setReg, gpr_arithFlags, hx, ite_false]
  · simp only [State.setMem_rd, rd_setReg, rd_arithFlags]
  · simp only [State.setMem_wr, wr_setReg, wr_arithFlags]

/-- `storeCtrAt`: the counter `r` blocks after the slot's first (`r9d = 16 + r`)
stored to `rax`. -/
theorem storeCtrAt_ok (s : State) {C : Block} {c r : Nat} (hS : SlotOk (s.gpr .r11) C (fun i => c + i) s.mem)
    (h9 : (s.gpr .r9).setWidth 32 = BitVec.ofNat 32 (16 + r))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 slot) 256) (hw : InRegions s.wr (s.gpr .rax) 16)
    (hd : Region.Disjoint ⟨s.gpr .rax, 16⟩ (slotR (s.gpr .r11))) :
    WP isa (.block Impl.Gcm.X86_64.Slot.storeCtrAt) s fun t =>
      blockAt t.mem (s.gpr .rax) = Nat.repeat inc32 (c + r) C ∧
      Frame [⟨s.gpr .rax, 16⟩] s.mem t.mem ∧ (∀ x, x ≠ .r10 → t.gpr x = s.gpr x) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ (∀ r, r ≠ .xmm13 → ∀ l, t.zlane r l = s.zlane r l) := by
  rw [Impl.Gcm.X86_64.Slot.storeCtrAt, WP.block_append_iff]
  refine WP.mono (storeCtr_ok s hS (VG.Proof.Gcm.X86_64.Stitch.in_pre hr (by decide)) hw)
    fun t ⟨hb, hm, hg, hrd, hwr, hz⟩ => ?_
  have hf₁ : Frame [⟨s.gpr .rax, 16⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine WP.mono (patch_ok t (by
      rw [hrd, hwr, hg, ← Offset.add_add]; exact VG.Proof.Gcm.X86_64.Stitch.in_sub hr (by decide))
    (by rw [hwr, hg]; exact VG.Proof.Gcm.X86_64.Stitch.in_sub hw (by decide))) fun u ⟨hm', hf'⟩ =>
      ⟨?_, ?_, fun x hx => by rw [hf'.gpr x hx, hg], by rw [hf'.rd, hrd], by rw [hf'.wr, hwr],
        fun x hx l => by rw [hf'.zlane, hz x hx l]⟩
  · have e : t.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 32 =
        s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (slot + 12)) 32 :=
      hf₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [← Offset.add_add]
        exact (hd.sub_right (Offset.sub_base _ (by decide))).symm) (by decide)
    have e16 : (BitVec.ofNat 32 (16 + r) - BitVec.signExtend 32 (16 : BitVec 32)) = BitVec.ofNat 32 r := by
      rw [show BitVec.signExtend 32 (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Nat.add_comm,
        BitVec.ofNat_add, BitVec.add_sub_cancel]
    rw [hm', hg, e, slot_ctr hS, h9, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, e16,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact refreshCounter_ok _ _ C c r hb
  · rw [hm', hg]
    exact hf₁.writeW List.mem_cons_self _ (Offset.contains_base (s.gpr .rax) (d := 12) (n := 4) (k := 16)
      (by decide) (by decide))

end VG.Proof.Gcm.X86_64.Slot
