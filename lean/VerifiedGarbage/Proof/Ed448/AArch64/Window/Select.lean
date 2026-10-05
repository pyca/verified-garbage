import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
import VerifiedGarbage.Proof.Curve448.AArch64.Swap
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow

/-!
# Ed448 verification on AArch64: the constant-time selection of a table entry

Untrusted: everything here is checked by Lean. For the digit `n < 16` in
`x11`, `digitMasks` leaves `maskReg m` all ones exactly for `m = n`
(`digitMasks_ok`); then `selectEntryWord w` loads word `w` of each of the 16
entries of the table at `TAB`, ANDs it with its mask and ORs it into `x9`, so
only entry `n`'s survives, and stores it into slots 6–8 (`selectEntry_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside store_ok)
open VG.Proof.Curve448.AArch64 (mask)

/-! ## The masks -/

private theorem mask_fact : ∀ n < 16, ∀ m < 16,
    (BitVec.ofNat 64 n - BitVec.ofNat 64 m) >>> 63 - (BitVec.ofNat 64 n - BitVec.ofNat 64 (m + 1)) >>> 63 =
      mask (decide (n = m)) := by
  decide +kernel

private theorem maskReg_ne : ∀ m < 16, maskReg m ≠ .x11 ∧ maskReg m ≠ .x10 ∧ maskReg m ≠ .x9 ∧
    maskReg m ≠ .x3 ∧ maskReg m ≠ .x12 ∧ maskReg m ≠ .x19 ∧ maskReg m ≠ .x20 := by decide

private theorem maskReg_inj : ∀ m < 16, ∀ j < 16, j ≠ m → maskReg j ≠ maskReg m := by decide

theorem digitMask_ok (s : State) {n m : Nat} (hn : n < 16) (hm : m < 16)
    (hx : s.gpr .x11 = BitVec.ofNat 64 n) :
    WP isa (.block (digitMask m)) s fun t =>
      t.gpr (maskReg m) = mask (decide (n = m)) ∧ Keeps [maskReg m, .x10] s t ∧ t.mem = s.mem := by
  obtain ⟨h11, h10, -, -, -, -, -⟩ := maskReg_ne m hm
  apply WP.of_runBlock
  simp only [digitMask, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show m + 1 < 4096 by omega, show m < 4096 by omega, show (63 : Nat) < 64 from by decide, ite_true,
    RegUpd.gpr_write, BitVec.setWidth_eq, Ne.symm h11, h10, Ne.symm h10, hx, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨mask_fact n hn m hm, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- The masks of the digit `n`. -/
def Masks16 (n : Nat) (s : State) : Prop := ∀ m < 16, s.gpr (maskReg m) = mask (decide (n = m))

/-- The registers `digitMasks` writes. -/
def maskClob : List Reg := .x10 :: maskRegs

theorem maskReg_mem {m : Nat} (hm : m < 16) : maskReg m ∈ maskClob := by
  revert m; decide

theorem digitMasks_ok (s : State) {n : Nat} (hn : n < 16) (hx : s.gpr .x11 = BitVec.ofNat 64 n) :
    WP isa (.block digitMasks) s fun t => Masks16 n t ∧ Keeps maskClob s t ∧ t.mem = s.mem := by
  suffices h : ∀ k ≤ 16, WP isa (.block ((List.range k).flatMap digitMask)) s fun t =>
      (∀ m < k, t.gpr (maskReg m) = mask (decide (n = m))) ∧ Keeps maskClob s t ∧ t.mem = s.mem from
    WP.mono (h 16 (Nat.le_refl _)) fun t ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩
  intro k hk
  induction k with
  | zero => exact WP.block_nil ⟨fun m hm => absurd hm (Nat.not_lt_zero _), Keeps.refl _ _, rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨tm, tk, tmem⟩ => ?_
    have tx : t.gpr .x11 = BitVec.ofNat 64 n := by
      rw [tk.1 _ (by decide)]; exact hx
    refine WP.mono (digitMask_ok t hn (by omega) tx) fun u ⟨um, uk, umem⟩ =>
      ⟨fun m hm => ?_, tk.trans (uk.mono ?_), umem.trans tmem⟩
    · by_cases hmk : m = k
      · subst hmk; exact um
      · rw [uk.1 _ ?_]
        · exact tm m (by omega)
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨maskReg_inj k (by omega) m (by omega) hmk, (maskReg_ne m (by omega)).2.1⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact maskReg_mem (by omega)
      · exact List.mem_cons_self

theorem Masks16.of_keeps {n : Nat} {rs : List Reg} {s t : State} (h : Masks16 n s) (k : Keeps rs s t)
    (hrs : ∀ m < 16, maskReg m ∉ rs) : Masks16 n t := fun m hm => by
  rw [k.1 _ (hrs m hm)]; exact h m hm

/-! ## A word of the entry -/

/-- Word `w` of entry `m` of the table. -/
def tw (m : Mem) (base : Addr) (e w : Nat) : BitVec 64 := word m base (TAB + 192 * e + 8 * w)

/-- Word `w` of entry `n` after the candidates `e ≤ k`, zero if `n > k`. -/
def selW (m : Mem) (base : Addr) (n k w : Nat) : BitVec 64 := if n ≤ k then tw m base n w else 0

private theorem or_and_zero (x y : BitVec 64) : x ||| (y &&& 0) = x := by ext i; simp

theorem selW_step (m : Mem) (base : Addr) (n k w : Nat) :
    selW m base n k w ||| (tw m base (k + 1) w &&& mask (decide (n = k + 1))) = selW m base n (k + 1) w := by
  unfold selW
  by_cases h : n ≤ k
  · simp only [h, ↓reduceIte, show n ≤ k + 1 by omega, show ¬ n = k + 1 by omega, decide_false,
      mask, Bool.false_eq_true]
    exact or_and_zero _ _
  · by_cases he : n = k + 1
    · subst he
      simp only [h, ↓reduceIte, Nat.le_refl, decide_true, mask, BitVec.and_allOnes]
      exact BitVec.zero_or
    · simp only [h, he, ↓reduceIte, show ¬ n ≤ k + 1 by omega, decide_false, mask, Bool.false_eq_true]
      exact or_and_zero _ _

theorem selW_zero (m : Mem) (base : Addr) (n w : Nat) :
    tw m base 0 w &&& mask (decide (n = 0)) = selW m base n 0 w := by
  unfold selW
  by_cases h : n = 0
  · subst h; simp only [decide_true, mask, ↓reduceIte, BitVec.and_allOnes, Nat.le_refl]
  · simp only [h, decide_false, mask, Bool.false_eq_true, ↓reduceIte, show ¬ n ≤ 0 by omega]
    exact BitVec.and_zero

/-- An `and` of `r` into `d`, from the registers. -/
theorem andReg_ok (s : State) (d r : Reg) :
    WP isa (.block [.logic .and .x d d r]) s fun t =>
      t.gpr d = s.gpr d &&& s.gpr r ∧ Keeps [d] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r' hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

/-- Candidate `e + 1`: its word loaded into `x10`, masked, ORed into `x9`. -/
theorem cand_ok {s : State} {base : Addr} (hs : Scr s base) {n e w : Nat} (he : e < 15) (hw : w < 24)
    (hm : s.gpr (maskReg (e + 1)) = mask (decide (n = e + 1))) :
    WP isa (.block [ld .x10 (TAB + 192 * (e + 1) + 8 * w), .logic .and .x .x10 .x10 (maskReg (e + 1)),
        .logic .orr .x .x9 .x9 .x10]) s fun t =>
      t.gpr .x9 = s.gpr .x9 ||| (tw s.mem base (e + 1) w &&& mask (decide (n = e + 1))) ∧
      Keeps [.x10, .x9] s t ∧ t.mem = s.mem := by
  obtain ⟨-, h10, -, -, -, -, -⟩ := maskReg_ne (e + 1) (by omega)
  rw [show ([ld .x10 (TAB + 192 * (e + 1) + 8 * w), .logic .and .x .x10 .x10 (maskReg (e + 1)),
      .logic .orr .x .x9 .x9 .x10] : List Instr) = [ld .x10 (TAB + 192 * (e + 1) + 8 * w)] ++
      [.logic .and .x .x10 .x10 (maskReg (e + 1)), .logic .orr .x .x9 .x9 .x10] from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok hs .x10 (d := TAB + 192 * (e + 1) + 8 * w)
    (by simp only [TAB]; omega) (by simp only [TAB]; omega)) fun a ⟨a10, ma, ka⟩ => ?_
  have am : a.gpr (maskReg (e + 1)) = s.gpr (maskReg (e + 1)) := ka.1 _ (by simpa using h10)
  have a9 : a.gpr .x9 = s.gpr .x9 := ka.1 _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, RegUpd.gpr_write,
    BitVec.setWidth_eq, ite_true, ite_false, a10, am, a9, hm,
    show (Reg.x9 = Reg.x10) = False from by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun r hr => ?_, ka.2.1, ka.2.2⟩, ma⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  exact ka.1 _ (by simpa using hr.1)

theorem cands_ok {s : State} {base : Addr} (hs : Scr s base) {n w : Nat} (hw : w < 24) (hm : Masks16 n s)
    (k : Nat) (hk : k ≤ 15) (h0 : s.gpr .x9 = selW s.mem base n 0 w) :
    WP isa (.block ((List.range k).flatMap fun e =>
        [ld .x10 (TAB + 192 * (e + 1) + 8 * w), .logic .and .x .x10 .x10 (maskReg (e + 1)),
          .logic .orr .x .x9 .x9 .x10])) s fun t =>
      t.gpr .x9 = selW s.mem base n k w ∧ Keeps [.x10, .x9] s t ∧ t.mem = s.mem := by
  induction k with
  | zero => exact WP.block_nil ⟨h0, Keeps.refl _ _, rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t9, kt, mt⟩ => ?_
    have ht : Scr t base := hs.of_keeps kt (by decide)
    have tm : Masks16 n t := hm.of_keeps kt fun m hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(maskReg_ne m hm).2.1, (maskReg_ne m hm).2.2.1⟩
    refine WP.mono (cand_ok ht (e := k) (by omega) hw (tm (k + 1) (by omega))) fun u ⟨u9, ku, mu⟩ =>
      ⟨?_, kt.trans ku, mu.trans mt⟩
    rw [u9, t9, mt, selW_step]

/-- Where word `w` of the selected entry goes: slots 6–8, eight words each. -/
def dst (w : Nat) : Nat := slot (6 + w / 8) + 8 * (w % 8)

theorem dst_bounds {w : Nat} (hw : w < 24) : 832 ≤ dst w ∧ dst w + 8 ≤ 1216 ∧ dst w % 8 = 0 := by
  simp only [dst, slot]; omega

theorem selectEntryWord_eq (w : Nat) :
    selectEntryWord w = [ld .x9 (TAB + 8 * w), .logic .and .x .x9 .x9 (maskReg 0)] ++
      ((List.range 15).flatMap fun e => [ld .x10 (TAB + 192 * (e + 1) + 8 * w),
        .logic .and .x .x10 .x10 (maskReg (e + 1)), .logic .orr .x .x9 .x9 .x10]) ++ [st .x9 (dst w)] := rfl

theorem selectEntryWord_ok {s : State} {base : Addr} (hs : Scr s base) {n w : Nat} (hn : n < 16) (hw : w < 24)
    (hm : Masks16 n s) :
    WP isa (.block (selectEntryWord w)) s fun t =>
      t.mem = s.mem.writeW (off base (dst w)) (tw s.mem base n w) ∧ Keeps [.x9, .x10] s t := by
  rw [selectEntryWord_eq, List.append_assoc, WP.block_append_iff]
  rw [show ([ld .x9 (TAB + 8 * w), .logic .and .x .x9 .x9 (maskReg 0)] : List Instr) =
    [ld .x9 (TAB + 8 * w)] ++ [.logic .and .x .x9 .x9 (maskReg 0)] from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok hs .x9 (d := TAB + 8 * w)
    (by simp only [TAB]; omega) (by simp only [TAB]; omega)) fun a ⟨a9, ma, ka⟩ => ?_
  refine WP.mono (andReg_ok a .x9 (maskReg 0)) fun b ⟨b9, kb, mb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  have b0 : b.gpr .x9 = selW b.mem base n 0 w := by
    rw [b9, a9, ka.1 _ (by decide), hm 0 (by decide), mb, ma, ← selW_zero]
    simp only [tw, Nat.mul_zero, Nat.add_zero]
  have bm : Masks16 n b := (hm.of_keeps ka fun m hm' => by
    simpa using (maskReg_ne m hm').2.2.1).of_keeps kb fun m hm' => by
    simpa using (maskReg_ne m hm').2.2.1
  rw [WP.block_append_iff]
  refine WP.mono (cands_ok hsb hw bm 15 (Nat.le_refl _) b0) fun c ⟨c9, kc, mc⟩ => ?_
  have hsc : Scr c base := hsb.of_keeps kc (by decide)
  obtain ⟨_, d2, d3⟩ := dst_bounds hw
  refine WP.mono (store_ok hsc (d := dst w) (by omega) d3 .x9)
    fun t ⟨mt, kt⟩ => ⟨?_, ?_⟩
  · rw [mt, c9, mc, mb, ma]
    simp only [selW, show n ≤ 15 by omega, ↓reduceIte]
  · exact (((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kc.mono (by decide))).trans
      (kt.mono (by decide))

theorem tw_write {m : Mem} {base : Addr} {w : Nat} (hw : w < 24) (v : BitVec 64) (e w' : Nat) (he : e < 16)
    (hw' : w' < 24) : tw (m.writeW (off base (dst w)) v) base e w' = tw m base e w' := by
  obtain ⟨d1, d2, d3⟩ := dst_bounds hw
  unfold tw
  rw [VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega)
    (by simp only [TAB]; omega) d3 (by simp only [TAB]; omega), ite_eq_right_iff.mpr]
  intro h; simp only [TAB] at h; omega

/-- **The selection** of the entry for the digit `n < 16` in `x11` into slots 6–8. -/
theorem selectEntry_ok {s : State} {base : Addr} (hs : Scr s base) {n : Nat} (hn : n < 16)
    (hx : s.gpr .x11 = BitVec.ofNat 64 n) :
    WP isa (.block selectEntry) s fun t =>
      (∀ w < 24, word t.mem base (dst w) = tw s.mem base n w) ∧ Outside base 832 384 s.mem t.mem ∧
      Keeps (.x9 :: maskClob) s t := by
  rw [selectEntry, WP.block_append_iff]
  refine WP.mono (digitMasks_ok s hn hx) fun a ⟨am, ka, ma⟩ => ?_
  have hsa : Scr a base := hs.of_keeps ka (by decide)
  suffices h : ∀ k ≤ 24, WP isa (.block ((List.range k).flatMap selectEntryWord)) a fun t =>
      (∀ w < k, word t.mem base (dst w) = tw s.mem base n w) ∧ Outside base 832 384 s.mem t.mem ∧
      (∀ e < 16, ∀ w < 24, tw t.mem base e w = tw s.mem base e w) ∧ Keeps [.x9, .x10] a t from
    WP.mono (h 24 (Nat.le_refl _)) fun t ⟨t1, t2, _, t4⟩ => ⟨t1, t2, (ka.mono (by decide)).trans (t4.mono (by decide))⟩
  intro k hk
  induction k with
  | zero => exact WP.block_nil ⟨fun w hw => absurd hw (Nat.not_lt_zero _),
      by rw [ma]; exact Outside.refl _ _ _ _, fun e _ w _ => by rw [ma], Keeps.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t1, t2, t3, kt⟩ => ?_
    have ht : Scr t base := hsa.of_keeps kt (by decide)
    have tm : Masks16 n t := am.of_keeps kt fun m hm' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(maskReg_ne m hm').2.2.1, (maskReg_ne m hm').2.1⟩
    refine WP.mono (selectEntryWord_ok ht hn (by omega) tm) fun u ⟨um, ku⟩ =>
      ⟨fun w hw => ?_, ?_, fun e he w hw => ?_, kt.trans ku⟩
    · obtain ⟨_, d2, d3⟩ := dst_bounds (show k < 24 by omega)
      obtain ⟨_, e2, e3⟩ := dst_bounds (show w < 24 by omega)
      rw [um, VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega)
        (by omega) d3 e3]
      by_cases hwk : w = k
      · subst hwk; rw [ite_eq_left rfl, t3 n hn w (by omega)]
      · rw [ite_eq_right (by simp only [dst, slot]; omega)]; exact t1 w (by omega)
    · obtain ⟨d1, d2, _⟩ := dst_bounds (show k < 24 by omega)
      rw [um]
      exact t2.trans ((VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega)).mono
        (by omega) (by omega))
    · rw [um, tw_write (by omega) _ e w he hw, t3 e he w hw]

end VG.Proof.Ed448.AArch64.Window
