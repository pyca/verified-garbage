module

public import VerifiedGarbage.Proof.Ecdh.X86_64.WinJac
public import VerifiedGarbage.Proof.Ecdh.X86_64.MulJ4
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacNorm
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Weierstrass.X86_64.AddConst
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ECDH on x86-64: `[d]P` by 5-bit windows with an affine table

`Cfg.mulQJA`: `mulQJ` (`WinJac.lean`) with the window method's table made
affine (`JacWinCfg.windowA`, `winJacA_ok`). Its inversion leaves `R.z^(p-2)`
in the selected entry's `X` (`E.x`, a slot of the grid). Written out
(`Cfg.invJA`, `invSpecJA`), it writes the temporary area and the working area
of `invWin`, over the table of the bits of `n - 2`, below the window's table
of bits. A call of `vg_<curve>_inv_mod_p` (`Cfg.invJACall`, `invSpecJACall`,
for six words) writes `ACC`, `PT` and its working area, which covers part of
the window's table of bits: the call keeps those bytes and `PT` in the table
of the bits of `n - 2` and puts them back. Either way, `mulQJA` writes what
`mulQJ` and the power write and that table (`mulQJAW`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-! ## The table's inversion -/

theorem invJA_acc (c : Cfg) : (Impl.Ecdh.X86_64.Cfg.invJA c).acc = c.sl (WT + 80) := by
  show c.sl WT + 16 * (40 * c.n) = _
  simp (disch := sl_ne) only [sl_eq]; unfold WT; omega_arith

/-- The working area ends below the window's table of bits. -/
theorem invTbl_below (h4 : 4 ≤ c.n) : bitsAt c.n 2 + invTbl c.n ≤ c.sl WB := by
  rw [bitsAt_eq]; simp (disch := sl_ne) only [sl_eq]; simp only [invTbl]; unfold WB; omega_arith

/-- The inversion of the window method with an affine table: its slots and
working area. -/
theorem invLayJA (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) :
    InvLay (Impl.Ecdh.X86_64.Cfg.invJA c) size := by
  have h7 := hc.n10
  have h4 : 4 ≤ c.n := by omega_arith
  have hT : bitsAt c.n 2 + invTbl c.n ≤ size := by
    have := invTbl_below h4; have := sl_le_jw c h46 (i := WB) (by decide); omega_arith
  have below : ∀ {i}, i < 45 → i ≠ TMP → c.sl i + 8 * c.n ≤ bitsAt c.n 2 := fun hi hT => by
    have := sl_below_bits c hi 2 0 (.inl hT); omega_arith
  have hacc := invJA_acc c
  have above : bitsAt c.n 2 + invTbl c.n ≤ c.sl (WT + 80) := by
    have := invTbl_below h4; have := sl_lt c (show WB < WT + 80 by decide); omega_arith
  refine ⟨h4, show c.n < 10 by omega_arith, ?_, sl_le c h7 (i := RZ) (by decide), hT,
    sl_le c h7 (i := MP) (by decide), sl_le c h7 (i := TMP) (by decide), ?_, ?_,
    Or.inl (below (by decide) (by decide)), ?_,
    (sl_apart_hi c (i := TMP) (by decide) (Nat.le_refl _) invW_below_tmp).symm, ?_,
    Or.inl (below (by decide) (by decide)),
    sl_apart c (by decide)⟩ <;> rw [hacc]
  · exact sl_le_jw c h46 (by decide)
  · exact sl_apart c (by decide)
  · exact Or.inr above
  · exact sl_apart c (by decide)
  · exact sl_apart c (by decide)

/-- The inversion as the window method takes it: `E.x = R.z^(p-2)`, writing
`E.x`, the temporary area and a working area apart from the window's slots and
table of bits. -/
theorem invSpecJA (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) {base : Addr} :
    InvSpecJ (jwQ c) c.C base size (InvCfg.inv (Impl.Ecdh.X86_64.Cfg.invJA c))
      (invW (Impl.Ecdh.X86_64.Cfg.invJA c)) := by
  obtain ⟨h4, sp, ip⟩ := hc.inv (by omega_arith)
  have h7 := hc.n10
  have hJle := jwinJ_le hc
  refine ⟨fun t ht hM hz => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · exact WP.mono (sp (invLayJA hc h46) (by have := hc.p_ge; omega_arith) (unitMod_pow_two hc.p_odd (64 * c.n))
      ht hM hz ⟨ip.B1, ip.B16, ip.C, ip.Cpos, ip.Cn, ip.bound⟩) fun t' ⟨a, b, d, e⟩ => ⟨a, b, d, e⟩
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ⟨Or.inl (show c.sl MP + 8 * c.n ≤ bitsAt c.n 2 by
        have := sl_below_bits c (i := MP) (by decide) 2 0; omega_arith), fun x hx => ?_⟩)
      rw [jwSlots_eq] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have key : ∀ i ∈ roJ ++ otherJ ++ gridJ, i < 45 ∨ WT ≤ i := by decide
      rcases key i hi with h | h
      · exact sl_apart_hi c h (Nat.le_refl _) invW_below_tmp
      · refine Or.inr ?_
        show bitsAt c.n 2 + invTbl c.n ≤ c.sl i
        have := invTbl_below h4
        have := sl_lt c (show WB < WT by decide)
        have : c.sl WT ≤ c.sl i := by
          simp (disch := sl_ne) only [sl_eq]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
        omega_arith
    · exact Or.inr (Or.inl rfl)
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    have hb : (jwQ c).bits = c.sl WB := rfl
    have hJ : (jwQ c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
    rw [hb, hJ]
    rcases hw with rfl | rfl | rfl
    · refine Or.inl ?_
      show c.sl WB + 5 * Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ (Impl.Ecdh.X86_64.Cfg.invJA c).acc
      rw [invJA_acc]; simp (disch := sl_ne) only [sl_eq]; unfold WB WT; omega_arith
    · exact Or.inr (invTbl_below h4)
    · by_cases h6 : c.n = 6
      · refine Or.inl ?_
        show c.sl WB + 5 * Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ c.sl TMP
        rw [sl_tmp6 c h6]; simp (disch := sl_ne) only [sl_eq]; unfold WB
        rw [h6] at hJle ⊢; omega_arith
      · exact Or.inr (sl_lt c (show TMP < WB by decide) (.inr (.inr ⟨h6, by decide⟩)))

/-- What the window method with an affine table writes, inversion included. -/
theorem invJA_w :
    ∀ w ∈ jwW (jwQ c) ++ invW (Impl.Ecdh.X86_64.Cfg.invJA c),
      w ∈ winXJ c ++ slW c (otherJ ++ gridJ ++ [TMP]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · rw [jwW_eq] at hw; exact List.mem_append_right _ hw
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · refine List.mem_append_right _ (List.mem_map.mpr ⟨WT + 80, by decide, ?_⟩)
      rw [invJA_acc]; rfl
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨TMP, by decide, rfl⟩)

/-! ## The table's inversion by a call -/

/-- Words that read the same, as numbers, are the same. -/
private theorem word_eq_of_wordsVal {m m' : Mem} {base : Addr} : ∀ {d k : Nat},
    wordsVal m base d k = wordsVal m' base d k → ∀ j < k, word m base (d + 8 * j) = word m' base (d + 8 * j)
  | _, 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | d, k + 1, h, j, hj => by
    simp only [wordsVal] at h
    have ha := (word m base d).isLt
    have hb := (word m' base d).isLt
    have e1 : (word m base d).toNat = (word m' base d).toNat := by omega_arith
    have e2 : wordsVal m base (d + 8) k = wordsVal m' base (d + 8) k := by omega_arith
    rcases j with _ | j
    · exact BitVec.eq_of_toNat_eq e1
    · have := word_eq_of_wordsVal e2 j (by omega_arith)
      rwa [show d + 8 + 8 * j = d + 8 * (j + 1) by omega_arith] at this

/-- Bytes whose word reads the same are the same. -/
private theorem byte_of_word {m m' : Mem} {base : Addr} {d : Nat} (h : word m base d = word m' base d)
    {j : Nat} (hj : j < 8) : m (off base d + BitVec.ofNat 64 j) = m' (off base d + BitVec.ofNat 64 j) := by
  have e := congrArg (fun v : BitVec 64 => v.extractLsb' (8 * j) 8) h
  change ((m.read (off base d) 8).setWidth 64).extractLsb' (8 * j) 8 =
    ((m'.read (off base d) 8).setWidth 64).extractLsb' (8 * j) 8 at e
  rw [BitVec.setWidth_eq, BitVec.setWidth_eq, Mem.extractLsb'_read _ _ hj, Mem.extractLsb'_read _ _ hj] at e
  exact e

/-- The bytes of words that read the same, as a number, are the same. -/
private theorem byte_of_wordsVal {m m' : Mem} {base : Addr} {d k : Nat}
    (h : wordsVal m base d k = wordsVal m' base d k) {x : Addr} (hx : d ≤ ofs base x)
    (hx' : ofs base x < d + 8 * k) : m x = m' x := by
  obtain ⟨j, hj, i, hi, rfl⟩ : ∃ j < k, ∃ i < 8, x = off base (d + 8 * j) + BitVec.ofNat 64 i := by
    refine ⟨(ofs base x - d) / 8, by omega_arith, (ofs base x - d) % 8, Nat.mod_lt _ (by decide), ?_⟩
    rw [off, Offset.add_add, show d + 8 * ((ofs base x - d) / 8) + (ofs base x - d) % 8 = ofs base x by omega_arith,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  exact byte_of_word (word_eq_of_wordsVal h j hj) hi

/-- What the call writes, but for the bytes it keeps: `E.x`, the table of the
bits of `n - 2`, the temporary area, `ACC`, and the function's working area
below the window's table of bits. -/
def invJACallW (c : Cfg) : List (Nat × Nat) :=
  [((jwQ c).E.x, 8 * c.n), (bitsAt c.n 2, invTbl c.n), (c.sl TMP, 8 * c.n), (c.sl ACC, 8 * c.n),
    (bitsAt c.n 3, c.sl WB - bitsAt c.n 3)]

/-- The places, for six words. -/
private theorem callLay (h6 : c.n = 6) :
    c.sl WB = 3568 ∧ bitsAt c.n 2 = 3008 ∧ bitsAt c.n 3 = 3400 ∧
    Impl.Ecdh.X86_64.Cfg.invJAWords c = 35 ∧ Impl.Ecdh.X86_64.Cfg.invJAPt c = 3288 ∧
    c.sl PT = 1504 ∧ c.sl ACC = 1456 ∧ c.sl RZ = 832 ∧ (jwQ c).E.x = 7936 ∧ c.sl TMP = 4048 ∧
    c.sl MP = 64 ∧ invTbl c.n = 448 ∧ (∀ i, i ≠ TMP → i ≠ 55 → i ≠ 83 → c.sl i = 64 + 48 * i) := by
  have hE : (jwQ c).E.x = c.sl (WT + 80) := invJA_acc c
  have hs : ∀ i, i ≠ TMP → i ≠ 55 → i ≠ 83 → c.sl i = 64 + 48 * i := fun i h1 h2 h3 => by
    rw [sl_eq c i ⟨h1, h2, h3⟩, h6]
  refine ⟨hs _ (by decide) (by decide) (by decide), by rw [bitsAt_eq, h6], by rw [bitsAt_eq, h6], ?_, ?_,
    hs _ (by decide) (by decide) (by decide), hs _ (by decide) (by decide) (by decide),
    hs _ (by decide) (by decide) (by decide), by rw [hE, hs _ (by decide) (by decide) (by decide)]; rfl,
    by rw [sl_tmp6 c h6, h6], hs _ (by decide) (by decide) (by decide), by simp only [invTbl, h6], hs⟩
  · unfold Impl.Ecdh.X86_64.Cfg.invJAWords
    rw [hs _ (by decide) (by decide) (by decide), bitsAt_eq, h6]; rfl
  · unfold Impl.Ecdh.X86_64.Cfg.invJAPt Impl.Ecdh.X86_64.Cfg.invJAWords
    rw [hs _ (by decide) (by decide) (by decide), bitsAt_eq, bitsAt_eq, h6]; rfl

/-- The inversion by a call, for six words: `E.x = R.z^(p-2)`, writing
`invJACallW`. -/
theorem invSpecJACall (hc : CfgOk c) (h6 : c.n = 6) (hi : c.inverse ≠ none) {base : Addr} :
    InvSpecJ (jwQ c) c.C base size (Impl.Ecdh.X86_64.Cfg.invJACall c) (invJACallW c) := by
  obtain ⟨eWB, eB2, eB3, eW, ePt, ePT, eACC, eRZ, eEx, eTMP, eMP, eT, hs⟩ := callLay h6
  have hJle := jwinJ_le hc
  have hb : (jwQ c).bits = c.sl WB := rfl
  have hJ : (jwQ c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
  have hsz : size = 8192 := rfl
  have hn6 : 8 * c.n = 48 := by rw [h6]
  have hMn : (jwQ c).M.n = c.n := rfl
  have hMmo : (jwQ c).M.mo = c.sl MP := rfl
  have hMtmp : (jwQ c).M.tmp = c.sl TMP := rfl
  -- The window's slots, numbered.
  have key : ∀ x ∈ jwSlots (jwQ c), ∃ i, x = 64 + 48 * i ∧ ((12 ≤ i ∧ i < 45 ∧ i ≠ ACC ∧ i ≠ PT) ∨
      i = PT ∨ (3 ≤ i ∧ i < 12) ∨ WT ≤ i) := by
    intro x hx
    rw [jwSlots_eq] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have k : ∀ i ∈ roJ ++ otherJ ++ gridJ, i ≠ TMP ∧ i ≠ 55 ∧ i ≠ 83 ∧
        ((12 ≤ i ∧ i < 45 ∧ i ≠ ACC ∧ i ≠ PT) ∨ i = PT ∨ (3 ≤ i ∧ i < 12) ∨ WT ≤ i) := by decide
    obtain ⟨k1, k2, k3, k4⟩ := k i hi
    exact ⟨i, hs i k1 k2 k3, k4⟩
  refine ⟨fun t ht hM hz => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · have hn := ht.nowrap
    rw [hMn] at hz
    unfold Impl.Ecdh.X86_64.Cfg.invJACall
    simp only [Code.inline]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (copy_ok (Impl.Ecdh.X86_64.Cfg.invJAWords c) ht (o := bitsAt c.n 2) (a := c.sl WB)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_
    have ht₁ := ht.of_keepRegs k₁ (by decide)
    refine WP.mono (copy_ok c.n ht₁ (o := Impl.Ecdh.X86_64.Cfg.invJAPt c) (a := c.sl PT)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun t₂ ⟨e₂, k₂, O₂⟩ => ?_
    have ht₂ := ht₁.of_keepRegs k₂ (by decide)
    have U₂ : Unch base [(bitsAt c.n 2, 8 * Impl.Ecdh.X86_64.Cfg.invJAWords c),
        (Impl.Ecdh.X86_64.Cfg.invJAPt c, 8 * c.n)] t.mem t₂.mem := O₁.unch.trans O₂.unch
    have hM₂ : ModOkW c.MP' size c.C.p t₂.mem base := hM.unch U₂ (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      show c.sl MP + 8 * c.n ≤ w.1 ∨ _
      rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) hn
    have z₂ : wordsVal t₂.mem base (c.sl RZ) c.n = wordsVal t.mem base (c.sl RZ) c.n :=
      U₂.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
    refine WP.seq (WP.mono (show WP isa c.pPow.inline t₂ fun s' => KeepRegs (invClob c.n) t₂ s' ∧
        Unch base (pwW c) t₂.mem s'.mem ∧ wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
          toM c.C.p (2 ^ (64 * c.n)) (wordsVal t₂.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) by
      unfold Cfg.pPow
      cases hi' : c.inverse with
      | none => exact absurd hi' hi
      | some C =>
        obtain ⟨h9, -⟩ := hc.inverse (by rw [hi']; rfl)
        exact WP.mono (invPFn_ok hc (by omega_arith) h9 ht₂ hM₂ (by rw [z₂]; exact hz)) fun _ h => h.2)
      fun t₃ ⟨K₃, U₃, lt₃, v₃⟩ => ?_)
    have ht₃ := ht₂.of_keepRegs K₃ (rdi_not_invClob _)
    have p₃ : ∀ x, (ofs base x < 1456 ∨ 1552 ≤ ofs base x) → (ofs base x < 3400 ∨ 3848 ≤ ofs base x) →
        (ofs base x < 4048 ∨ 4096 ≤ ofs base x) → t₃.mem x = t₂.mem x := fun x h1 h2 h3 =>
      U₃ x fun w hw => by
        simp only [pwW, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (copy_ok c.n ht₃ (o := (jwQ c).E.x) (a := c.sl ACC) (by omega_arith) (by omega_arith) (by omega_arith))
      fun t₄ ⟨e₄, k₄, O₄⟩ => ?_
    have ht₄ := ht₃.of_keepRegs k₄ (by decide)
    refine WP.mono (copy_ok c.n ht₄ (o := c.sl PT) (a := Impl.Ecdh.X86_64.Cfg.invJAPt c) (by omega_arith)
      (by omega_arith) (by omega_arith)) fun t₅ ⟨e₅, k₅, O₅⟩ => ?_
    have ht₅ := ht₄.of_keepRegs k₅ (by decide)
    refine WP.mono (copy_ok (Impl.Ecdh.X86_64.Cfg.invJAWords c) ht₅ (o := c.sl WB) (a := bitsAt c.n 2)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun t₆ ⟨e₆, k₆, O₆⟩ => ?_
    have hrax : ∀ r ∈ [Reg.rax], r ∈ invClob c.n := fun r hr => by
      rw [List.mem_singleton.mp hr]; simp [invClob, powClob, clob]
    -- What the call and the copies after it keep.
    have far : ∀ x, (ofs base x < 1456 ∨ 1552 ≤ ofs base x) → (ofs base x < 3400 ∨ 3848 ≤ ofs base x) →
        (ofs base x < 4048 ∨ 4096 ≤ ofs base x) → (ofs base x < 7936 ∨ 7984 ≤ ofs base x) →
        t₄.mem x = t₂.mem x := fun x h1 h2 h3 h4 => by
      rw [O₄ x (by omega_arith), p₃ x h1 h2 h3]
    have U₄ : Unch base [(1456, 96), (3400, 448), (4048, 48), (7936, 48)] t₂.mem t₄.mem := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
      exact far x (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    have W4 : ∀ {d k : Nat}, 3008 ≤ d → d + 8 * k ≤ 3400 →
        wordsVal t₄.mem base d k = wordsVal t₂.mem base d k := fun h1 h2 =>
      U₄.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
    have B : wordsVal t₅.mem base (bitsAt c.n 2) 35 = wordsVal t.mem base (c.sl WB) 35 := by
      rw [O₅.wordsVal (by omega_arith) (by omega_arith), W4 (by omega_arith) (by omega_arith), O₂.wordsVal (by omega_arith) (by omega_arith),
        ← eW, e₁]
    have P : wordsVal t₄.mem base (Impl.Ecdh.X86_64.Cfg.invJAPt c) c.n = wordsVal t.mem base (c.sl PT) c.n := by
      rw [W4 (by omega_arith) (by omega_arith), e₂, O₁.wordsVal (by omega_arith) (by omega_arith)]
    have X : wordsVal t₆.mem base (jwQ c).E.x c.n = wordsVal t₃.mem base (c.sl ACC) c.n := by
      rw [O₆.wordsVal (by omega_arith) (by omega_arith), O₅.wordsVal (by omega_arith) (by omega_arith), e₄]
    refine ⟨((((k₁.mono hrax).trans (k₂.mono hrax)).trans K₃).trans ((k₄.mono hrax).trans
      ((k₅.mono hrax).trans (k₆.mono hrax)))), fun x hx => ?_, by rw [hMn, X]; exact lt₃, ?_⟩
    · simp only [invJACallW, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
      rw [eEx, eB2, eT, eTMP, eACC, eB3, eWB, hn6] at hx
      by_cases hb' : 3568 ≤ ofs base x ∧ ofs base x < 3848
      · -- The window's bits, put back.
        refine byte_of_wordsVal (base := base) (d := c.sl WB) (k := 35) (x := x) ?_ (by omega_arith) (by omega_arith)
        rw [← B, ← eW, e₆]
      · by_cases hp : 1504 ≤ ofs base x ∧ ofs base x < 1552
        · -- `PT`, put back.
          rw [O₆ x (by omega_arith)]
          refine byte_of_wordsVal (base := base) (d := c.sl PT) (k := c.n) (x := x) ?_ (by omega_arith) (by omega_arith)
          rw [e₅, P]
        · rw [O₆ x (by omega_arith), O₅ x (by omega_arith), far x (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
            O₂ x (by omega_arith), O₁ x (by omega_arith)]
    · show toM _ _ _ = toM _ _ _ ^ _
      rw [hMn, X, v₃, z₂]; rfl
  · simp only [invJACallW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [hMn, hMmo, hMtmp]
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ⟨Or.inl (by dsimp only; omega_arith), fun x hx => ?_⟩)
      obtain ⟨i, rfl, hi⟩ := key x hx
      dsimp only; unfold WT ACC PT at hi; omega_arith
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr ⟨Or.inl (by dsimp only; omega_arith), fun x hx => ?_⟩)
      obtain ⟨i, rfl, hi⟩ := key x hx
      dsimp only; unfold WT ACC PT at hi; omega_arith
    · refine Or.inr (Or.inr ⟨Or.inl (by dsimp only; omega_arith), fun x hx => ?_⟩)
      obtain ⟨i, rfl, hi⟩ := key x hx
      dsimp only; unfold WT ACC PT at hi; omega_arith
  · simp only [invJACallW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rw [hb, hJ]
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- What the inversion of `mulQJA`'s table writes, a call or written out. -/
def invJAW (c : Cfg) : List (Nat × Nat) :=
  if c.n = 6 ∧ c.inverse.isSome then invJACallW c else invW (Impl.Ecdh.X86_64.Cfg.invJA c)

theorem invSpecJAP (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) {base : Addr} :
    InvSpecJ (jwQ c) c.C base size (Impl.Ecdh.X86_64.Cfg.invJAProg c) (invJAW c) := by
  unfold Impl.Ecdh.X86_64.Cfg.invJAProg invJAW
  split
  · next h => exact invSpecJACall hc h.1 (fun e => by simp [e] at h)
  · exact invSpecJA hc h46

/-- What the window method with an affine table writes, inversion included,
within what `mulQJ`, its inversion and the power may write. -/
theorem invJAP_w (h46 : c.n = 4 ∨ c.n = 6) :
    ∀ w ∈ jwW (jwQ c) ++ invJAW c, ∃ w' ∈ winXJ c ++ slW c (otherJ ++ gridJ ++ [TMP]) ++ pwW c,
      w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact ⟨w, List.mem_append_left _ (invJA_w w (List.mem_append_left _ hw)), Nat.le_refl _, Nat.le_refl _⟩
  · unfold invJAW at hw
    split at hw
    · simp only [invJACallW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · refine ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨WT + 80, by decide, ?_⟩)),
          Nat.le_refl _, Nat.le_refl _⟩
        show (c.sl (WT + 80), 8 * c.n) = ((jwQ c).E.x, 8 * c.n)
        rw [← invJA_acc c]; rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_singleton_self _))), Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨TMP, by decide, rfl⟩)),
          Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨ACC, by decide, rfl⟩)),
          Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)),
          Nat.le_refl _, ?_⟩
        dsimp only
        rw [bitsAt_eq]; simp (disch := sl_ne) only [sl_eq]; unfold WB
        rcases h46 with h | h <;> rw [h] <;> omega_arith
    · exact ⟨w, List.mem_append_left _ (invJA_w w (List.mem_append_right _ hw)), Nat.le_refl _, Nat.le_refl _⟩

/-! ## `[d]P` and `Z^(p-2)` -/

/-- What `mulQJA` and the power may write: what `mulQJ` and the power may, and
the inversion's working area (`winXJ`). -/
abbrev mulQJAW (c : Cfg) : List (Nat × Nat) := winXJ c ++ slW c mulJI ++ pwW c

theorem mulQJA_w (hc : CfgOk c) : MulW c (mulQJAW c) where
  fixed := (fixedOk_winXJ.append (fixedOk_slW mulJI_idx)).append fixedOk_pwW
  d := apart_append (apart_append (apart_winXJ (by decide)) (apart_slW (by decide))) (apart_pwW (by decide) (by decide))
  flag := fun w hw => by
    have := hc.n0
    rcases apart_append (apart_append (apart_winXJ (c := c) (i := FLAG) (by decide))
      (apart_slW (l := mulJI) (by decide))) (apart_pwW (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h

/-- The Jacobian window method with an affine table computes `[d]P` for
`d < n` (`MulOk`), as `mulQJ_ok`. -/
theorem mulQJA_ok (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) (hC : Law c.C) (hO : PrimeOrder c.C)
    {dbl : Pt → Prog isa} (hD : DblOk c.MP' c.rcbSlots c.C dbl) (hn17 : 17 ≤ c.C.n % 32)
    (hn64 : 64 ≤ c.C.n) : MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJA c dbl) (mulQJAW c) := by
  intro base s hs g F hbp P hP hpx hpy hrep _ _ _ k hk hk8 _ ht₁ rest R h
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hJle := jwinJ_le hc
  unfold Impl.Ecdh.X86_64.Cfg.mulQJA
  refine WP.seq (WP.seq (WP.mono (maskK_ok hc hs (hk ▸ hk8)) fun s₁ ⟨hs₁, k₁, e₁, U₁⟩ => ?_))
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [K]) (by decide)) U₁
  have v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hne =>
    sv_unch U₁ h7 hn hi (apart_slW (by simpa using hne))
  -- `d mod 2^nbits + offset J` and its bits.
  have hk₁ : sv c base s₁ K < 2 ^ c.nbits := by rw [e₁]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hrec : wordsVal s₁.mem base (c.sl K) c.n + JacWinCfg.offset (Impl.Ecdh.X86_64.Cfg.jwinJ c) <
      32 ^ Impl.Ecdh.X86_64.Cfg.jwinJ c := recodeJ_lt hk₁
  have hJ : (jwQ c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WK <;> omega_arith
  have hKW := sl_lt c (show K < WK by decide)
  have h32 : (32 : Nat) ^ Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (32 : Nat) = 2 ^ 5 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  have e82 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := sl_ne) only [sl_eq]; unfold WK WB; omega_arith
  have hBs : c.sl WB + 80 * c.n ≤ size := by
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WB <;> omega_arith
  rw [Impl.Ecdh.X86_64.Cfg.jwinPrep]
  refine WP.seq (WP.seq ?_)
  rw [hK]
  refine WP.mono (addConst_ok hs₁ (n := c.n) (src := c.sl K) (dst := c.sl WK)
    (c := JacWinCfg.offset (Impl.Ecdh.X86_64.Cfg.jwinJ c)) h0 (sl_le c h7 (by decide)) (by omega_arith)
    (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [hB]
  refine WP.mono (bits_ok hs₂ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [e₂] at b₃
  have U₃ : Unch base (winX c) s₁.mem s₃.mem :=
    ((O₂.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega_arith)).unch.trans
      ((O₃.mono (o' := c.sl WB) (n' := 80 * c.n) (Nat.le_refl _) (by omega_arith)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  have F₃ := F₁.unch h7 hn fixedOk_winX U₃
  have e₃ : ∀ {i}, i < 45 → i ≠ K → sv c base s₃ i = sv c base s i := fun hi hne =>
    (sv_unch U₃ h7 hn hi (apart_winX hi)).trans (v₁ hi hne)
  have hM₃ := modP_of hc F₃.mp
  have tv : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₃ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hne => by show toM _ _ (sv c base s₃ _) = toM _ _ (sv c base s _); rw [e₃ hi hne]
  have hF : JacWinFixed (jwQ c) c.C base s₃ P (sv c base s₁ K) := by
    refine ⟨F₃.zero, fun x hx => ?_, ?_, ?_, fun t ht => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt_of_eq_of_lt (e₃ (i := PX) (by decide) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₃ (i := PY) (by decide) (by decide)) hpy
      · exact lt_of_eq_of_lt F₃.onep (Nat.mod_lt _ (by omega_arith))
    · show Rep _ (tmv c.C c.n base s₃ (c.sl PX)) (tmv c.C c.n base s₃ (c.sl PY))
        (tmv c.C c.n base s₃ (c.sl ONEP)) P
      rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]; exact hrep
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (c.sl ONEP) c.n) = 1
      rw [F₃.onep, show 2 ^ (64 * c.n) % c.C.p = c.mont 1 by simp [Cfg.mont, Cfg.R], toM_cmont hc]; rfl
    · rw [hJ] at ht
      exact b₃ t (by omega_arith)
  refine WP.mono (winJacA_ok (jwLayQ hc h46) hpR hC hc.am3 hO hD hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hn17 hn64 hP
    (by rw [hJ]; exact hrec) (invSpecJAP hc h46) hs₃ hM₃ hF) fun s₄ ⟨K₄, U₄', M₄, L₄, R₄⟩ => ?_
  have U₄ : Unch base (winXJ c ++ slW c (otherJ ++ gridJ ++ [TMP]) ++ pwW c) s₃.mem s₄.mem :=
    U₄'.cover (invJAP_w h46)
  have hs₄ := hs₃.of_keepRegs K₄ (rdi_not_invClob _)
  have F₄ := F₃.unch h7 hn ((fixedOk_winXJ.append (fixedOk_slW (by decide))).append fixedOk_pwW) U₄
  have rz₄ : wordsVal s₄.mem base (c.sl RZ) c.n < c.C.p :=
    L₄ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pPow_ok hc hs₄ M₄ rz₄ F₄.onep (fun h9 => absurd (by omega_arith) h9))
    fun s₅ ⟨K₅, U₅, lt₅, v₅⟩ => h s₅ ?_)
  have r₅ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₅ i = sv c base s₄ i := fun hi h₁ =>
    sv_unch U₅ h7 hn hi (apart_pwW hi h₁)
  have c₂ : ∀ r ∈ [Reg.rax, .r8], r ∈ invClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [invClob, powClob, clob]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (r8_mem_clob _))
  have c₃ : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ invClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [invClob, powClob, clob]
  have c₁ : ∀ r ∈ [Reg.r8], r ∈ invClob c.n := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (r8_mem_clob _))
  have KK : KeepRegs (invClob c.n) s s₄ :=
    (((k₁.mono c₁).trans (k₂.mono c₂)).trans (k₃.mono c₃)).trans K₄
  refine ⟨hs₄.of_keepRegs K₅ (rdi_not_invClob _), by
      rw [K₅.gpr _ (rsi_not_invClob _), KK.gpr _ (rsi_not_invClob _)], by rw [K₅.rd, KK.rd],
    by rw [K₅.wr, KK.wr], ((U₁.trans U₃).trans (U₄.trans U₅)).mono ?_, fun _ hlt => ?_, lt₅, ?_, ?_⟩
  · intro w hw
    have m1 : ∀ w ∈ winXJ c, w ∈ mulQJAW c := fun w h => List.mem_append_left _ (List.mem_append_left _ h)
    have m2 : ∀ w ∈ slW c mulJI, w ∈ mulQJAW c := fun w h => List.mem_append_left _ (List.mem_append_right _ h)
    have m3 : ∀ w ∈ pwW c, w ∈ mulQJAW c := fun w h => List.mem_append_right _ h
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with h | h
      · exact m2 _ (slW_mono (by decide) h)
      · exact m1 _ (List.mem_append_left _ h)
    · rcases List.mem_append.mp hw with hw | h
      · rcases List.mem_append.mp hw with hw | h
        · rcases List.mem_append.mp hw with h | h
          · exact m1 _ h
          · exact m2 _ (slW_mono (l' := mulJI) (fun _ hi => List.mem_append_left _ hi) h)
        · exact m3 _ h
      · exact m3 _ h
  · show Rep _ (toM _ _ (sv c base s₅ RX)) (toM _ _ (sv c base s₅ RY)) (toM _ _ (sv c base s₅ RZ)) _
    rw [r₅ (i := RX) (by decide) (by decide), r₅ (i := RY) (by decide) (by decide),
      r₅ (i := RZ) (by decide) (by decide)]
    have hq := R₄ (by rw [e₁, hk, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hc.n_bits)]; exact hlt)
    rw [e₁, hk, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hc.n_bits)] at hq
    exact hq
  · show _ = toM _ _ (sv c base s₅ RZ) ^ _
    rw [r₅ (i := RZ) (by decide) (by decide)]
    exact v₅
  · rw [r₅ (i := RZ) (by decide) (by decide)]; exact rz₄

end VG.Proof.Ecdh.X86_64
