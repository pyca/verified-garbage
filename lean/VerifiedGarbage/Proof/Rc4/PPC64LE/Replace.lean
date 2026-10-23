module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Lookup
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-! # RC4 on PPC64LE: replacing a secret-indexed byte of the table -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Proof.Rc4

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-! ## Moving the difference to the byte's lane -/

/-- The difference `c`, once lanes `7, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 64 :=
  if jj ≤ L then (c.setWidth 64) <<< (8 * (L - jj)) else 0#64

theorem rot_zero : (0#64).rotateRight 56 = 0#64 := by decide

theorem spread_succ (c : Byte) {L j : Nat} (hL : L < 8) :
    (spread c L (j + 1)).rotateRight 56 ||| (if L = j then c.setWidth 64 else 0#64) =
      spread c L j := by
  unfold spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, rot_byte c (by omega), ite_eq_right (show ¬ L = j by omega),
      BitVec.or_zero, ite_eq_left (show j ≤ L by omega), show L - (j + 1) + 1 = L - j by omega]
  · rw [ite_eq_right h1, rot_zero, BitVec.zero_or]
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega)]

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 8)
    (h9 : s.gpr .r9 = idx.setWidth 64) (h8 : s.gpr .r8 = 0) (hax : s.gpr .r10 = c.setWidth 64)
    (h11 : s.gpr .r11 = spread c (idx.toNat % 8) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .r11 = spread c (idx.toNat % 8) j ∧ t.gpr .r10 = s.gpr .r10 ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.mem = s.mem := by
  unfold spreadStep laneMask isZero
  rrun [h9, h8, hax, h11, show j < 2 ^ 15 by omega]
  rw [lane_mask idx hj, and_allOnes_ite, spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (h8 : s₀.gpr .r8 = 0) (hax : s₀.gpr .r10 = c.setWidth 64) :
    ∀ n ≤ 8, ∀ s, s.gpr .r11 = spread c (idx.toNat % 8) n → s.gpr .r10 = s₀.gpr .r10 →
      s.gpr .r9 = s₀.gpr .r9 → s.gpr .r8 = s₀.gpr .r8 → s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .r11 = spread c (idx.toNat % 8) 0 ∧ t.gpr .r10 = s₀.gpr .r10 ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s h11 hax' _ _ hm; exact WP.block_nil ⟨h11, hax', hm⟩
  | succ n ih =>
    intro s h11 hax' h9' h8' hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (spread_step s idx c (by omega) (h9'.trans h9) (h8'.trans h8)
      (hax'.trans hax) h11) fun t ⟨t11, tax, t9, t8, tm⟩ => ?_
    exact ih (by omega) t t11 (tax.trans hax') (t9.trans h9') (t8.trans h8') (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 8).reverse := rfl

/-! ## Storing back every doubleword -/

/-- The memory once doublewords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) : Mem :=
  if n / 8 < k then
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) :
    (scatter m p n d k).writeW (p + BitVec.ofNat 64 (8 * k))
      ((scatter m p n d k).readW (p + BitVec.ofNat 64 (8 * k)) 64 ^^^
        (if n / 8 = k then d else 0#64)) = scatter m p n d (k + 1) := by
  unfold scatter
  by_cases h0 : n / 8 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 8 = k by omega), BitVec.xor_zero, writeW_readW,
      ite_eq_left (show n / 8 < k + 1 by omega)]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 8 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 8 < k + 1 by omega), h1]
    · rw [ite_eq_right h1, BitVec.xor_zero, writeW_readW,
        ite_eq_right (show ¬ n / 8 < k + 1 by omega)]

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h9 : s.gpr .r9 = idx.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hw : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r3 + BitVec.ofNat 64 (8 * k))
        (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * k)) 64 ^^^
          (if idx.toNat / 8 = k then s.gpr .r11 else 0#64)) ∧
      t.gpr .r11 = s.gpr .r11 ∧ t.gpr .r9 = s.gpr .r9 ∧ t.gpr .r8 = s.gpr .r8 ∧
      t.gpr .r3 = s.gpr .r3 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * k)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scatterStep rowMask isZero
  rrun [h9, h8, hr, hw, show 8 * k < 2 ^ 15 by omega, show (8 * k) % 4 = 0 by omega]
  rw [row_mask idx hk, allOnes_and_ite]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 64)
    (h9 : s₀.gpr .r9 = idx.setWidth 64) (h8 : s₀.gpr .r8 = 0)
    (hw : InRegions s₀.wr (s₀.gpr .r3) 256) :
    ∀ n ≤ 32, ∀ s, s.gpr .r11 = d → s.gpr .r9 = s₀.gpr .r9 → s.gpr .r8 = s₀.gpr .r8 →
      s.gpr .r3 = s₀.gpr .r3 → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (s₀.gpr .r3) idx.toNat d n ∧ t.gpr .r11 = d ∧
        t.gpr .r9 = s₀.gpr .r9 ∧ t.gpr .r8 = s₀.gpr .r8 ∧ t.gpr .r3 = s₀.gpr .r3 ∧
        t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s h11 h9' h8' hp hwr hm
    refine WP.block_nil ⟨?_, h11, h9', h8', hp, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h11 h9' h8' hp hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h11 h9' h8' hp hwr hm) fun t ⟨tm, t11, t9, t8, tp, twr⟩ => ?_
    have hq : InRegions t.wr (t.gpr .r3 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [twr, tp]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hw
    refine WP.mono (scatter_step t idx (by omega) (t9.trans h9) (t8.trans h8) hq)
      fun u ⟨um, u11, u9, u8, up, _, uwr⟩ => ?_
    refine ⟨?_, u11.trans t11, u9.trans t9, u8.trans t8, up.trans tp, uwr.trans twr⟩
    rw [um, tm, t11, tp, scatter_succ]

/-! ## The replacement -/

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem replace_core (s : State) (idx ii : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (h8 : s.gpr .r8 = 0) (hcx : s.gpr .r6 = ii.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r3) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r3 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 ii.toNat) 1 :=
    region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  have hit : InRegions (s.rd ++ s.wr) (s.gpr .r3 + ii.setWidth 64) 1 := by
    rw [byte_addr]; exact hi
  let p := s.gpr .r3
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (lookup_core s idx h9 h8 hr) (by decide +kernel))
    fun t ⟨⟨tax, tm⟩, tk⟩ => ?_
  have t9 : t.gpr .r9 = s.gpr .r9 := tk.gpr (by decide)
  have t8 : t.gpr .r8 = s.gpr .r8 := tk.gpr (by decide)
  have tp : t.gpr .r3 = s.gpr .r3 := tk.gpr (by decide)
  have tcx : t.gpr .r6 = s.gpr .r6 := tk.gpr (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  have h1 : WP isa (.block (loadI ++ ([.logic .xor .r10 .r10 .r0, .li .r11 0] : List Instr))) t
      fun u =>
      u.gpr .r10 = (b ^^^ v).setWidth 64 ∧ u.gpr .r11 = 0 ∧ u.gpr .r9 = s.gpr .r9 ∧
        u.gpr .r8 = s.gpr .r8 ∧ u.gpr .r3 = s.gpr .r3 ∧ u.gpr .r6 = s.gpr .r6 ∧ u.mem = s.mem ∧
        u.rd = s.rd ∧ u.wr = s.wr := by
    unfold loadI
    rrun [hit, tax, tm, t9, t8, tp, tcx, tk.2.1, tk.2.2, hcx]
    rw [byte_addr ii, xor_byte]
  refine WP.mono h1 fun u ⟨uax, u11, u9, u8, up, ucx, um, urd, uwr⟩ => ?_
  rw [WP.block_append_iff]
  have hsp := spread_steps u idx (b ^^^ v) (u9.trans h9) (u8.trans h8) uax 8 (by decide) u
    (by rw [u11]; unfold spread; rw [ite_eq_right (by omega)]; rfl) rfl rfl rfl rfl
  rw [← lanesDown_eq] at hsp
  refine WP.mono (WP.keep [.r0, .r11, .r12] hsp (by decide +kernel))
    fun w ⟨⟨w11, wax, wm⟩, wk⟩ => ?_
  have w9 : w.gpr .r9 = s.gpr .r9 := (wk.gpr (by decide)).trans u9
  have w8 : w.gpr .r8 = s.gpr .r8 := (wk.gpr (by decide)).trans u8
  have wp : w.gpr .r3 = s.gpr .r3 := (wk.gpr (by decide)).trans up
  have wcx : w.gpr .r6 = s.gpr .r6 := (wk.gpr (by decide)).trans ucx
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  rw [← List.append_assoc, WP.block_append_iff]
  have h2 : WP isa (.block (loadI ++ ([.logic .xor .r10 .r10 .r0] : List Instr))) w
      fun x => x.gpr .r10 = b.setWidth 64 ∧ x.gpr .r11 = w.gpr .r11 ∧ x.gpr .r9 = s.gpr .r9 ∧
        x.gpr .r8 = s.gpr .r8 ∧ x.gpr .r3 = s.gpr .r3 ∧ x.mem = s.mem ∧ x.wr = s.wr := by
    unfold loadI
    rrun [hit, wax, uax, wm, um, w9, w8, wp, wcx, wwr, wrd, hcx]
    rw [byte_addr ii, xor_byte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, x11, x9, x8, xp, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.r0, .r12]
    (scatter_steps s idx _ h9 h8 hw 32 (by decide) x rfl x9 x8 xp xwr xm)
    (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, x11, w11]
  unfold scatter spread
  rw [ite_eq_left (by omega), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.PPC64LE
