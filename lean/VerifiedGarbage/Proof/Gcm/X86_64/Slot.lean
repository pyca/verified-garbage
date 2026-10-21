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
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock
public import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev

/-!
# AES-GCM's counter blocks in memory

`Impl.Gcm.X86_64.Slot`'s code, for working space at `p` (in `r11`): the
sixteen blocks at `p + slot` are counter blocks of `C` (`SlotOk`), and `ecx`
holds the 32 bits `inc₃₂` increments of the first. `put_ok`: one block's
last four bytes written from `ecx`, which advances.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Slot

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Gcm.X86_64.Slot (slot put puts refill loads ctrsM)
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

/-- Scalar code that keeps everything but `rcx`, the flags and memory. -/
structure CFrame (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rcx → t.gpr r = s.gpr r
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

/-- One block's last four bytes, at `r11 + slot + 16 i + 12`, from `ecx`
byte-reversed; `ecx` advanced. -/
theorem put_ok (s : State) (i : Nat)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12)) 4) :
    WP isa (.block (put i)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12))
        (bswap32 ((s.gpr .rcx).setWidth 32)) ∧
      (t.gpr .rcx).setWidth 32 = (s.gpr .rcx).setWidth 32 + 1 ∧ CFrame s t := by
  suffices h : WP isa (.block (put i)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12))
        (bswap32 ((s.gpr .rcx).setWidth 32)) ∧
      (t.gpr .rcx).setWidth 32 = (s.gpr .rcx).setWidth 32 + 1 ∧ (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧
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

/-- The memory after `puts n` from `ecx = v`, with the working space at `p`. -/
def putsMem (m : Mem) (p : Addr) (v : BitVec 32) : Nat → Mem
  | 0 => m
  | n + 1 => (putsMem m p v n).writeW (p + BitVec.ofNat 64 (slot + 16 * n + 12)) (bswap32 (v + BitVec.ofNat 32 n))

theorem puts_ok (n : Nat) (s : State)
    (hw : ∀ i < n, InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12)) 4) :
    WP isa (.block (puts n)) s fun t =>
      t.mem = putsMem s.mem (s.gpr .r11) ((s.gpr .rcx).setWidth 32) n ∧
      (t.gpr .rcx).setWidth 32 = (s.gpr .rcx).setWidth 32 + BitVec.ofNat 32 n ∧ CFrame s t := by
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

/-- `puts n` from `ecx = lo(C) + t` makes blocks `i < n` `inc₃₂^(t + i)(C)`,
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

/-- `puts n` writes only the slot. -/
theorem putsMem_frame (m : Mem) (p : Addr) (v : BitVec 32) : ∀ n, n ≤ 16 → Frame [slotR p] m (putsMem m p v n)
  | 0, _ => Frame.refl _ _
  | n + 1, hn => (putsMem_frame m p v n (by omega)).writeW List.mem_cons_self _ (by
      rw [show slot + 16 * n + 12 = slot + (16 * n + 12) by omega, ← Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega))

/-- `add ecx, d` (or `sub ecx, d`, `op`), from its 32-bit result. -/
theorem rcx32_ok (op : AluOp) (v : BitVec 32) (s : State) (r : BitVec 32)
    (hr : op = .add ∧ r = (s.gpr .rcx).setWidth 32 + v ∨ op = .sub ∧ r = (s.gpr .rcx).setWidth 32 - v) :
    WP isa (.block [.alu32 op .rcx (.imm v)]) s fun t =>
      (t.gpr .rcx).setWidth 32 = r ∧ t.mem = s.mem ∧ CFrame s t := by
  suffices h : WP isa (.block [.alu32 op .rcx (.imm v)]) s fun t =>
      (t.gpr .rcx).setWidth 32 = r ∧ t.mem = s.mem ∧ (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr from
    WP.mono (WP.zvecKeep (c := .block [.alu32 op .rcx (.imm v)]) (by rcases hr with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl) h)
      fun t ⟨⟨hc, hm, hg, hrd, hwr⟩, hx, hy, hz⟩ => ⟨hc, hm, ⟨hg, hx, hy, hz, hrd, hwr⟩⟩
  apply WP.of_runBlock
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, readSrc32, execAlu32, State.setReg32,
    gpr_setReg, gpr_arithFlags, ↓reduceIte, Option.bind_some, setWidth_setWidth_32, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, Option.some.injEq, exists_eq_left', true_and] <;>
  exact ⟨fun x hx => by simp only [hx, ite_false], trivial⟩

/-- `refill d`: the slot advanced by `d` blocks, and `ecx` with it. -/
theorem refill_ok (d : Nat) (s : State) {C : Block} {c : Nat}
    (hS : SlotOk (s.gpr .r11) C (fun i => c + i) s.mem)
    (hc : (s.gpr .rcx).setWidth 32 = C.extractLsb' 0 32 + BitVec.ofNat 32 c)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 slot) 256) :
    WP isa (.block (refill d)) s fun t =>
      SlotOk (s.gpr .r11) C (fun i => c + d + i) t.mem ∧
      (t.gpr .rcx).setWidth 32 = C.extractLsb' 0 32 + BitVec.ofNat 32 (c + d) ∧
      Frame [slotR (s.gpr .r11)] s.mem t.mem ∧ CFrame s t := by
  rw [refill, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (rcx32_ok .add _ s _ (.inl ⟨rfl, rfl⟩)) fun t ⟨hc₁, hm₁, hf₁⟩ => ?_
  have hw' : ∀ i < 16, InRegions t.wr (t.gpr .r11 + BitVec.ofNat 64 (slot + 16 * i + 12)) 4 := fun i hi => by
    rw [hf₁.wr, hf₁.gpr .r11 (by decide), show slot + 16 * i + 12 = slot + (16 * i + 12) by omega,
      ← Offset.add_add]
    exact VG.Proof.Gcm.X86_64.Stitch.in_sub hw (by omega)
  refine WP.mono (puts_ok 16 t hw') fun u ⟨hm₂, hc₂, hf₂⟩ => ?_
  refine WP.mono (rcx32_ok .sub 16 u _ (.inr ⟨rfl, rfl⟩)) fun w ⟨hc₃, hm₃, hf₃⟩ => ?_
  have hp : t.gpr .r11 = s.gpr .r11 := hf₁.gpr .r11 (by decide)
  have hv : (t.gpr .rcx).setWidth 32 = C.extractLsb' 0 32 + BitVec.ofNat 32 (c + d) := by
    rw [hc₁, hc, BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨?_, ?_, ?_, (hf₁.trans hf₂).trans hf₃⟩
  · rw [hm₃, hm₂, hp, hv]
    have := putsMem_ok (p := s.gpr .r11) (C := C) (f := fun i => c + i) (m := t.mem) (t := c + d) 16
      (Nat.le_refl _) (by rw [hm₁]; exact hS) (fun i _ => by omega)
    intro i hi
    simpa only [hi, ite_true] using this i hi
  · rw [hc₃, hc₂, hv]; exact BitVec.add_sub_cancel _ _
  · rw [hm₃, hm₂, hp, hm₁]
    exact putsMem_frame _ _ _ 16 (Nat.le_refl _)

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
of register `k` block `4 k + l` (as `VaesZ.ctrsZ_ok`), and the slot and
`ecx` advance to the next group. -/
theorem ctrsM_ok (rs : List XReg) (s : State) {C : Block} {c : Nat}
    (hS : SlotOk (s.gpr .r11) C (fun i => c + i) s.mem)
    (hc : (s.gpr .rcx).setWidth 32 = C.extractLsb' 0 32 + BitVec.ofNat 32 c)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 slot) 256)
    (hk : rs.length ≤ 4) (hnd : rs.Nodup) :
    WP isa (.block (ctrsM rs)) s fun t =>
      (∀ k (h : k < rs.length), ∀ l < 4,
        t.zlane rs[k] l = XBinOp.eval .pshufb (Nat.repeat inc32 (c + 4 * k + l) C) revMask) ∧
      SlotOk (s.gpr .r11) C (fun i => c + 4 * rs.length + i) t.mem ∧
      (t.gpr .rcx).setWidth 32 = C.extractLsb' 0 32 + BitVec.ofNat 32 (c + 4 * rs.length) ∧
      Frame [slotR (s.gpr .r11)] s.mem t.mem ∧ (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r, r ∉ rs → ∀ l < 4, t.zlane r l = s.zlane r l) := by
  rw [ctrsM, WP.block_append_iff]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 slot) 256 :=
    VG.Proof.Aes.X86_64.AesNi.inRegions_wr hw
  refine WP.mono (loads_ok rs 0 s hS (by omega) hnd hin) fun t ⟨hL, hf⟩ => ?_
  refine WP.mono (refill_ok (4 * rs.length) t (C := C) (c := c) (by rw [hf.gpr, hf.mem]; exact hS) (by rw [hf.gpr]; exact hc)
    (by rw [hf.gpr, hf.wr]; exact hw)) fun u ⟨hS', hc', hm', hf'⟩ => ?_
  rw [hf.gpr] at hS' hm'
  refine ⟨fun k hk l hl => ?_, hS', hc', by rw [← hf.mem]; exact hm',
    fun r hr => by rw [hf'.gpr r hr, hf.gpr], by rw [hf'.rd, hf.rd], by rw [hf'.wr, hf.wr],
    fun r hr l hl => by rw [hf'.zlane, hf.zlane r hr l hl]⟩
  rw [hf'.zlane, hL k hk l hl, show 4 * (0 + k) + l = 4 * k + l by omega, Nat.add_assoc]

end VG.Proof.Gcm.X86_64.Slot
