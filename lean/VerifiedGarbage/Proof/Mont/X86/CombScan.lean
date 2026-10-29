module

public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Loop
import Init.Data.BitVec.Basic
import VerifiedGarbage.Proof.Mont.X86.ArgFar
/-! Fixed-address comb selection: each iteration writes one selected table word. -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/CombSelectMath.lean`, which only this module imported.
section

/-! Wordwise masked comb lookup reuses the window equality masks. -/

section
namespace VG.Proof.Mont.X86.Dynamic

/-- Accumulating the fixed-address loads returns the selected word, or zero
until its entry has been visited. No secret table index is needed. -/
theorem masked_words_prefix (value : Nat → BitVec 32) (index count : Nat) :
    (List.range count).foldl (fun acc j =>
      acc ||| (value j &&& (if index = j then BitVec.allOnes 32 else 0#32))) 0#32 =
      if index < count then value index else 0#32 := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    by_cases eq : index = count
    · subst index
      simp only [Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceIte, BitVec.and_allOnes, BitVec.zero_or]
    · have same : index < count + 1 ↔ index < count := by omega
      simp only [eq, ↓reduceIte, BitVec.and_zero, BitVec.or_zero, same]

/-- The actual subtract/shift mask used by x86 has the same lookup result
for all 32 entries of the shared RSA comb. -/
theorem masked_words_lookup (value : Nat → BitVec 32) {index : Nat} (hi : index < 32) :
    (List.range 32).foldl (fun acc j =>
      acc ||| (value j &&& (0#32 - (((BitVec.ofNat 32 index ^^^ BitVec.ofNat 32 j) - 1) >>> 31)))) 0#32 =
      value index := by
  have same : ∀ j ∈ List.range 32, ∀ acc : BitVec 32,
      acc ||| (value j &&& (0#32 - (((BitVec.ofNat 32 index ^^^ BitVec.ofNat 32 j) - 1) >>> 31))) =
      acc ||| (value j &&& (if index = j then BitVec.allOnes 32 else 0#32)) := by
    intro j hj acc
    exact congrArg (fun mask : BitVec 32 => acc ||| (value j &&& mask))
      (window_mask_small index hi j (List.mem_range.mp hj))
  have congr_fold {f g : BitVec 32 → Nat → BitVec 32} (l : List Nat)
      (eq : ∀ j ∈ l, ∀ acc, f acc j = g acc j) : ∀ acc, l.foldl f acc = l.foldl g acc := by
    induction l with
    | nil => intro acc; rfl
    | cons j l ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [eq j (by simp), ih (fun k hk => eq k (by simp [hk]))]
  rw [congr_fold (List.range 32) same, masked_words_prefix, ite_eq_left hi]

end VG.Proof.Mont.X86.Dynamic
end

end

-- Formerly `VerifiedGarbage/Proof/Mont/X86/MaskedLoad.lean`, which only this module imported.
section

/-! One fixed-address masked table load, shared across table widths. -/

section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem maskedWord_ok {s : State} {table mask : MemOp} {value maskValue : BitVec 32}
    (ht : readSrc s (.mem table) = some value) (hm : readSrc s (.mem mask) = some maskValue)
    (base : mask.base ≠ .eax) :
    WP isa (.block (VG.Impl.Mont.X86.Comb.maskedWord table mask)) s fun t =>
      t.mem = s.mem ∧ t.gpr .ebx = s.gpr .ebx ||| (value &&& maskValue) ∧
      Keeps [.eax, .ebx] s t := by
  unfold VG.Impl.Mont.X86.Comb.maskedWord
  refine wp_movS ht fun u₁ U₁ _ => ?_
  refine wp_logicS (.inl rfl) (by rw [readSrc_upd U₁ base]; exact hm) fun u₂ U₂ => ?_
  refine wp_orS rfl fun t U₃ => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact U₃.mem.trans (U₂.mem.trans U₁.mem)
  · rw [U₃.gpr, U₂.gpr, U₁.gpr, U₂.other .ebx (by decide), U₁.other .ebx (by decide)]
    rfl
  · exact ((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps

/-- Read-only instructions preserve fixed memory operands whose base registers
are outside the accumulator pair. -/
theorem readSrc_mask_keeps {s t : State} {m : MemOp}
    (M : t.mem = s.mem) (K : Keeps [.eax, .ebx] s t)
    (h : m.base ∉ [.eax, .ebx]) : readSrc t (.mem m) = readSrc s (.mem m) := by
  show t.load32 (t.ea m) = s.load32 (s.ea m)
  have addr : t.ea m = s.ea m := by simp only [State.ea, K.1 _ h]
  simp only [State.load32, addr, M, K.2.1, K.2.2]

/-- The emitted full scan accumulates the same fold as the masked lookup
algebra. No memory is written and no table-dependent address is formed. -/
theorem maskedWords_ok (js : List Nat) {s : State}
    (table mask : Nat → MemOp) (value masks : Nat → BitVec 32)
    (ht : ∀ j ∈ js, readSrc s (.mem (table j)) = some (value j))
    (hm : ∀ j ∈ js, readSrc s (.mem (mask j)) = some (masks j))
    (tb : ∀ j ∈ js, (table j).base ∉ [.eax, .ebx])
    (mb : ∀ j ∈ js, (mask j).base ∉ [.eax, .ebx]) :
    WP isa (.block (js.flatMap fun j => VG.Impl.Mont.X86.Comb.maskedWord (table j) (mask j))) s fun t =>
      t.mem = s.mem ∧
      t.gpr .ebx = js.foldl (fun acc j => acc ||| (value j &&& masks j)) (s.gpr .ebx) ∧
      Keeps [.eax, .ebx] s t := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | cons j js ih =>
    simp only [List.flatMap_cons]
    refine WP.block_append (WP.mono (maskedWord_ok (ht j (by simp)) (hm j (by simp))
      (by have := mb j (by simp); simp only [List.mem_cons, List.not_mem_nil, or_false,
        not_or] at this; exact this.1)) fun u ⟨M, V, K⟩ => ?_)
    refine WP.mono (ih (s := u)
      (fun k hk => (readSrc_mask_keeps M K (tb k (by simp [hk]))).trans (ht k (by simp [hk])))
      (fun k hk => (readSrc_mask_keeps M K (mb k (by simp [hk]))).trans (hm k (by simp [hk])))
      (fun k hk => tb k (by simp [hk])) (fun k hk => mb k (by simp [hk]))) fun t ⟨M', V', K'⟩ => ?_
    exact ⟨M'.trans M, by simpa only [List.foldl_cons, V] using V', K.trans K'⟩

/-- A complete 32-entry instruction scan returns the indexed word. The index
is used only in the mask values, never in an address operand. -/
theorem maskedLookup_ok {s : State} (table mask : Nat → MemOp)
    (value : Nat → BitVec 32) {index : Nat} (hi : index < 32)
    (ht : ∀ j < 32, readSrc s (.mem (table j)) = some (value j))
    (hm : ∀ j < 32, readSrc s (.mem (mask j)) =
      some (if index = j then BitVec.allOnes 32 else 0#32))
    (tb : ∀ j < 32, (table j).base ∉ [.eax, .ebx])
    (mb : ∀ j < 32, (mask j).base ∉ [.eax, .ebx]) :
    WP isa (.block (.mov .ebx (.imm 0) :: (List.range 32).flatMap fun j =>
      VG.Impl.Mont.X86.Comb.maskedWord (table j) (mask j))) s fun t =>
      t.mem = s.mem ∧ t.gpr .ebx = value index ∧ Keeps [.eax, .ebx] s t := by
  refine wp_movS rfl fun u U _ => ?_
  have K : Keeps [.eax, .ebx] s u := U.keeps.mono (by decide)
  refine WP.mono (maskedWords_ok (List.range 32) table mask value
    (fun j => if index = j then BitVec.allOnes 32 else 0#32)
    (fun j hj => (readSrc_mask_keeps U.mem K (tb j (List.mem_range.mp hj))).trans
      (ht j (List.mem_range.mp hj)))
    (fun j hj => (readSrc_mask_keeps U.mem K (mb j (List.mem_range.mp hj))).trans
      (hm j (List.mem_range.mp hj)))
    (fun j hj => tb j (List.mem_range.mp hj)) (fun j hj => mb j (List.mem_range.mp hj)))
    fun t ⟨M, V, K'⟩ => ?_
  refine ⟨M.trans U.mem, ?_, K.trans K'⟩
  rw [U.gpr] at V
  change t.gpr .ebx = (List.range 32).foldl _ 0#32 at V
  simpa only [masked_words_prefix, hi, ↓reduceIte] using V

end VG.Proof.Mont.X86.Dynamic
end

end

-- Formerly `VerifiedGarbage/Proof/Mont/X86/CombMasks.lean`, which only this module imported.
section

/-! The comb's equality masks occupy a fixed, otherwise unused scratch range. -/

section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- Prepare all equality masks, preserving the table, window index and every
byte outside the mask range. -/
theorem combMasks_ok {s : State} {base : Addr} {size mask : Nat}
    (hs : Scr s base size) (hmask : 8 ≤ mask) (hw : w32 s.mem base 4 < 32) :
    ∀ k, k ≤ 32 → mask + 4*k ≤ size →
    WP isa (.block ((List.range k).flatMap fun j =>
      VG.Impl.Mont.X86.Dynamic.windowMask j ++ ([.store (sc (mask+4*j)) .ecx] : List Instr))) s fun t =>
      Outside base mask (4*k) s.mem t.mem ∧
      (∀ j < k, t.mem.readW (off base (mask+4*j)) 32 =
        if w32 s.mem base 4 = j then BitVec.allOnes 32 else 0) ∧
      Keeps [.eax, .ecx] s t
  | 0, _, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by omega, Keeps.refl _ _⟩
  | k+1, hk, hz => by
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    refine WP.block_append (WP.mono (combMasks_ok hs hmask hw k (by omega) (by omega))
      fun u ⟨O, V, K⟩ => ?_)
    have hu := hs.of_keeps K (by decide)
    have win : w32 u.mem base 4 = w32 s.mem base 4 := O.w32 (by omega) (by omega)
    refine WP.block_append (WP.mono (windowMask_ok hu (by omega) (by rw [win]; exact hw) (by omega))
      fun v ⟨M, C, K'⟩ => ?_)
    have hv := hu.of_keeps K' (by decide)
    refine wp_storeS (hv.ea (d := mask+4*k) (by omega))
      (hv.write (d := mask+4*k) (n := 4) (by omega)) fun t W => WP.block_nil ?_
    have nw := hs.nowrap
    have F : Outside base (mask+4*k) 4 u.mem t.mem := by
      rw [W.mem, M]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(O.mono (Nat.le_refl _) (by omega)).trans (F.mono (by omega) (by omega)), ?_,
      (K.trans K').trans (W.keeps _)⟩
    intro j hj
    by_cases eq : j = k
    · subst j
      rw [W.mem, Mem.readW_writeW_self32, C, win]
    · have jl : j < k := by omega
      have same := F.w32 (d := mask+4*j) (by omega) (by omega)
      apply BitVec.eq_of_toNat_eq
      change w32 t.mem base (mask+4*j) = _
      rw [same]
      exact congrArg BitVec.toNat (V j jl)

end VG.Proof.Mont.X86.Dynamic
end

end

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
