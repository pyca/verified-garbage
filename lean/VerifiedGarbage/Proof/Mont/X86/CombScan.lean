module

import VerifiedGarbage.Proof.Mont.X86.MaskedLoad
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Mont.X86.CombMasks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Proof.Mont.Words32

/-! Fixed-address comb selection: each iteration writes one selected table word. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

/-- The entire 32-entry table and mask array are disjoint from the destination. -/
structure CombScanLay (n tab dst mask size : Nat) : Prop where
  positive : 0 < n
  table : tab + 256*n ≤ size
  output : dst + 8*n ≤ size
  masks : mask + 128 ≤ size
  table_apart : dst + 8*n ≤ tab ∨ tab + 256*n ≤ dst
  masks_apart : dst + 8*n ≤ mask ∨ mask + 128 ≤ dst

theorem CombScanLay.entry {n tab dst mask size : Nat} (_L : CombScanLay n tab dst mask size)
    {j : Nat} (hj : j < 32) :
    tab ≤ entry n tab j ∧ entry n tab j + 8*n ≤ tab+256*n := by
  have H := Nat.mul_le_mul_left (8*n) (show j+1 ≤ 32 by omega)
  simp only [Nat.mul_add, Nat.mul_one] at H
  unfold VG.Impl.Mont.X86.Dynamic.entry
  omega

/-- One instruction iteration preserves every byte except its output word,
returns the selected word, and advances the public pointer and loop flag. -/
theorem combScanStep_ok {s : State} {base : Addr} {size n tab dst mask index i : Nat}
    (hs : Scr s base size) (L : CombScanLay n tab dst mask size)
    (hi : i < 2*n) (hx : index < 32)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4*i))
    (hm : ∀ j < 32, s.mem.readW (off base (mask+4*j)) 32 =
      if index = j then BitVec.allOnes 32 else 0) :
    WP isa (.block (VG.Impl.Mont.X86.Comb.scanStep n tab dst 32 (fun j => sc (mask+4*j)))) s fun t =>
      Outside base (dst+4*i) 4 s.mem t.mem ∧
      t.mem.readW (off base (dst+4*i)) 32 = s.mem.readW (off base (entry n tab index+4*i)) 32 ∧
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4*(i+1)) ∧
      t.zf = some (decide (i+1 = 2*n)) ∧ Keeps [.eax, .ebx, .ebp] s t := by
  have out := L.output
  have masks := L.masks
  have nw := hs.nowrap
  have width : 4*(2*n) < 2^32 := by have := hs.size_lt; omega
  unfold VG.Impl.Mont.X86.Comb.scanStep
  refine WP.block_append (WP.mono (maskedLookup_ok
    (fun j => at_ .ebp (entry n tab j)) (fun j => sc (mask+4*j))
    (fun j => s.mem.readW (off base (entry n tab j+4*i)) 32) hx
    (fun j hj => readSrc_at' hs hp (by have := L.entry hj; have := L.table; omega))
    (fun j hj => (readSrc_sc hs (d := mask+4*j) (by omega)).trans (congrArg some (hm j hj)))
    (by intros; exact of_decide_eq_true rfl) (by intros; exact of_decide_eq_true rfl)) fun u ⟨M, V, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  have pu : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4*i) := by
    rw [K.1 .ebp (by decide), K.1 .edi (by decide), hp]
  refine wp_storeS (hu.ea_at' pu (d := dst) (by omega))
    (hu.write (d := dst+4*i) (n := 4) (by omega)) fun v W => ?_
  refine wp_addS rfl fun v₁ U₁ _ => ?_
  refine wp_movS rfl fun v₂ U₂ _ => ?_
  refine wp_addS rfl fun v₃ U₃ _ => ?_
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  have Kt : Keeps [.eax, .ebx, .ebp] s t :=
    (((((K.mono (by decide)).trans (W.keeps _)).widen U₁.keeps).widen U₂.keeps).widen U₃.keeps).trans (F.keeps _)
  have Mt : t.mem = v.mem := by rw [F.mem, U₃.mem, U₂.mem, U₁.mem]
  have pt : v₃.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4*i) + 4 := by
    rw [U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr, W.gpr, pu, K.1 .edi (by decide)]
    rfl
  have atEnd : v₃.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (8*n) := by
    rw [U₃.gpr, U₂.gpr, U₁.other _ (by decide), W.gpr, K.1 .edi (by decide)]
  refine ⟨?_, ?_, ?_, ?_, Kt⟩
  · rw [Mt, W.mem, M]; exact writeW32_outside _ _ _ (by omega)
  · rw [Mt, W.mem, Mem.readW_writeW_self32, V]
  · rw [Kt.1 .edi (by decide), F.gpr, pt, row_ebp]
  · rw [pt, atEnd] at Z
    simpa only [show 8*n = 4*(2*n) by omega, row_zf _ hi width] using Z

/-- The complete scan copies exactly the selected table entry and preserves
all other bytes, including all masks and every table entry. -/
theorem combScan_ok {s : State} {base : Addr} {size n tab dst mask index : Nat}
    (hs : Scr s base size) (L : CombScanLay n tab dst mask size) (hx : index < 32)
    (hm : ∀ j < 32, s.mem.readW (off base (mask+4*j)) 32 =
      if index = j then BitVec.allOnes 32 else 0) :
    WP isa (VG.Impl.Mont.X86.Comb.scan n tab dst 32 (fun j => sc (mask+4*j))) s fun t =>
      Outside base dst (8*n) s.mem t.mem ∧
      wordsVal t.mem base dst n = wordsVal s.mem base (entry n tab index) n ∧
      Keeps [.eax, .ebx, .ebp] s t := by
  have output := L.output
  have table := L.table
  have masks := L.masks
  have apart := L.table_apart
  have mapart := L.masks_apart
  have ent := L.entry hx
  have nw := hs.nowrap
  let I (i : Nat) (t : State) : Prop :=
    Outside base dst (4*i) s.mem t.mem ∧
    val32 t.mem base dst i = val32 s.mem base (entry n tab index) i ∧
    Keeps [.eax, .ebx, .ebp] s t ∧
    t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4*i)
  unfold VG.Impl.Mont.X86.Comb.scan
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have init : I 0 u := by
    refine ⟨?_, rfl, U.keeps.mono (by decide), ?_⟩
    · rw [U.mem]; exact Outside.refl _ _ _ _
    · rw [U.gpr, U.other .edi (by decide)]; exact (BitVec.add_zero _).symm
  refine WP.loop (M := isa) (fun m t => ∃ i, m = 2*n-i ∧ i < 2*n ∧ I i t)
    ?_ (2*n) u ⟨0, rfl, by have := L.positive; omega, init⟩
  rintro m t ⟨i, rfl, hi, O, V, K, P⟩
  have ht := hs.of_keeps K (by decide)
  have mt : ∀ j < 32, t.mem.readW (off base (mask+4*j)) 32 =
      if index = j then BitVec.allOnes 32 else 0 := by
    intro j hj
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem base (mask+4*j) = _
    rw [O.w32 (by omega) (by omega)]
    exact congrArg BitVec.toNat (hm j hj)
  refine WP.mono (combScanStep_ok ht L hi hx P mt) fun v ⟨F, W, P', Z, K'⟩ => ?_
  have next : I (i+1) v := by
    refine ⟨(O.mono (Nat.le_refl _) (by omega)).trans (F.mono (by omega) (by omega)), ?_,
      K.trans K', P'⟩
    rw [val32_succ, val32_succ, F.val32 (by omega) (by omega), V]
    have word : w32 v.mem base (dst+4*i) = w32 s.mem base (entry n tab index+4*i) := by
      change (v.mem.readW _ 32).toNat = _
      rw [W]
      exact O.w32 (by omega) (by omega)
    rw [word]
  by_cases done : i+1 = 2*n
  · refine .inl ⟨?_, ?_⟩
    · simp only [eval, Z, done, decide_true, Option.map_some, Bool.not_true]
    · rcases next with ⟨O', V', K'', _⟩
      rw [done] at O' V'
      refine ⟨?_, ?_, K''⟩
      · simpa only [show 4*(2*n) = 8*n by omega] using O'
      · simpa only [wordsVal_eq_val32] using V'
  · refine .inr ⟨?_, 2*n-(i+1), by omega, i+1, rfl, by omega, next⟩
    simp only [eval, Z, done, decide_false, Option.map_some, Bool.not_false]

/-- Mask preparation followed by the scan implements the complete private
lookup. The mask and destination ranges are the only writable bytes. -/
theorem wordSelectBody_ok {s : State} {base : Addr} {size n tab dst mask : Nat}
    (hs : Scr s base size) (L : CombScanLay n tab dst mask size)
    (hmask : 8 ≤ mask) (hw : w32 s.mem base 4 < 32)
    (sep : mask+128 ≤ tab ∨ tab+256*n ≤ mask) :
    WP isa (VG.Impl.Mont.X86.Comb.wordSelectBody n tab dst 32 (fun j => sc (mask+4*j))) s fun t =>
      Outs base [(mask, 128), (dst, 8*n)] s.mem t.mem ∧
      wordsVal t.mem base dst n = wordsVal s.mem base (entry n tab (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ebx, .ecx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.wordSelectBody
  refine WP.seq (WP.mono (combMasks_ok hs hmask hw 32 (by decide) L.masks) fun u ⟨O, V, K⟩ => ?_)
  refine WP.mono (combScan_ok (hs.of_keeps K (by decide)) L hw V) fun t ⟨O', V', K'⟩ => ?_
  refine ⟨(Outs.of_outside O (by simp)).trans (Outs.of_outside O' (by simp)), ?_,
    (K.mono (by decide)).trans (K'.mono (by decide))⟩
  rw [V']
  have ent := L.entry hw
  have table := L.table
  exact O.wordsVal (by omega) (by have := hs.nowrap; omega)

end VG.Proof.Mont.X86.Dynamic
