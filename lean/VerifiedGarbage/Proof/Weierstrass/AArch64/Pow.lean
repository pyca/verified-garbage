import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.Pow

/-!
# Short Weierstrass curves on AArch64: powers

`pow P` leaves `[acc]` reading (in Montgomery form) as `[base]^e`, for the
exponent `e` whose bits are the table at `P.bits` (`pow_ok`): an iteration
squares the accumulator, multiplies it by the base into `[tmp]` and keeps
that product if the exponent's bit is set (`powBody_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- The registers a power changes. -/
def powClob (n : Nat) : List Reg := .x19 :: clob n

theorem x19_not_clob (n : Nat) : Reg.x19 ∉ clob n := by
  intro h
  simp only [clob, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h | h | h | h | h | h <;> exact absurd h (by decide)
  · have := List.mem_of_mem_take h
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at this

/-- A power's slots, modulus and table at offsets that loads and stores can
encode. -/
structure PowA (P : PowCfg) : Prop where
  acc : P.acc % 8 = 0
  tmp : P.tmp % 8 = 0
  base : P.base % 8 = 0
  one : P.one % 8 = 0
  mod : ModA P.M
  bits : P.bits < 4096

/-- The loop's invariant at `x19 = j`: the accumulator reads as
`B^(e >>> j)`, for `B` what the base reads as at the start. -/
structure PowInv (P : PowCfg) (base : Addr) (size m e : Nat) [NeZero m] (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (powClob P.M.n) s₀ s
  unch : Unch base (powW P) s₀.mem s.mem
  lt : wordsVal s.mem base P.acc P.M.n < m
  val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) =
    toM m (2 ^ (64 * P.M.n)) (wordsVal s₀.mem base P.base P.M.n) ^ (e >>> j)

/-- An iteration. -/
theorem powBody_ok {P : PowCfg} {base : Addr} {size m e : Nat} [NeZero m] (hL : PowLay P size)
    (hA : PowA P) (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ : State} (hM₀ : ModOk P.M size m s₀.mem base)
    (hB : wordsVal s₀.mem base P.base P.M.n < m)
    (hbits : ∀ t < P.nbits, s₀.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ P.nbits) (hI : PowInv P base size m e s₀ s j) :
    WP isa (powBody P) s fun s' =>
      PowInv P base size m e s₀ s' (j - 1) ∧ s'.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
  have hn := hI.scr.nowrap
  have hnb := hL.nbits
  have hmo := hL.mo_w
  have hbw := hL.base_w
  have hacc := hL.acc
  have htmp := hL.tmp
  have hat := hL.acc_tmp
  have ham := hL.acc_mtmp
  have hmo' := hM₀.mo
  have hbase := hL.base
  have hbl := hL.bits
  have hM : ModOk P.M size m s.mem base :=
    ⟨hM₀.n0, hM₀.n7, hM₀.mo, hM₀.tmp, hM₀.sep,
      by rw [hI.unch.wordsVal hmo (by omega)]; exact hM₀.val, hM₀.inv⟩
  have hBs : wordsVal s.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n :=
    hI.unch.wordsVal hbw (by omega)
  -- `x19 -= 1` and `acc = acc²`.
  rw [powBody]
  refine WP.seq ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (decCounter_ok s hj (by omega) hI.x19) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.mem
  refine WP.mono (mul_ok hs₁ (hm₁ ▸ hM) hA.mod hacc hacc hacc hA.acc hA.acc hA.acc
    (by rw [hm₁]; exact hI.lt)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
  have hs₂ := k₂.scr hs₁
  have hM₂ : ModOk P.M size m s₂.mem base :=
    ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, by
      rw [k₂.unch.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hmo _ (by simp [powW])
        · exact hmo _ (by simp [powW])) (by omega), hm₁]; exact hM.val, hM.inv⟩
  have v₂ : toM m (2 ^ (64 * P.M.n)) (wordsVal s₂.mem base P.acc P.M.n) =
      toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) ^ 2 := by
    rw [toM_mul hm (e₂.trans (by rw [hm₁])), Lean.Grind.Semiring.pow_two]
  have hB₂ : wordsVal s₂.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n := by
    rw [k₂.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hbw _ (by simp [powW])
      · exact hbw _ (by simp [powW])) (by omega), hm₁, hBs]
  -- `tmp = acc · base`.
  refine WP.seq ?_
  refine WP.mono (mul_ok hs₂ hM₂ hA.mod htmp hacc hL.base hA.tmp hA.acc hA.base
    (by rw [hB₂]; exact hB)) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_
  have hs₃ := k₃.scr hs₂
  have hA₃ : wordsVal s₃.mem base P.acc P.M.n = wordsVal s₂.mem base P.acc P.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact ham) (by omega)
  have v₃ : toM m (2 ^ (64 * P.M.n)) (wordsVal s₃.mem base P.tmp P.M.n) =
      toM m (2 ^ (64 * P.M.n)) (wordsVal s₂.mem base P.acc P.M.n) *
        toM m (2 ^ (64 * P.M.n)) (wordsVal s₀.mem base P.base P.M.n) := by
    rw [toM_mul hm e₃, hB₂]
  -- The mask of bit `j - 1`, and the selection.
  have hU₃ : Unch base (powW P) s₀.mem s₃.mem := by
    refine ((hI.unch.trans (by rw [← hm₁]; exact k₂.unch)).trans k₃.unch).mono fun w hw => ?_
    simp only [powW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  have hbyte : s₃.mem (off base (P.bits + (j - 1))) = if e.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (fun w hw => by have := hL.bits_w w hw; omega) (by omega), hbits _ (by omega)]
  have hx19₃ : s₃.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
    rw [k₃.gpr _ (x19_not_clob _), k₂.gpr _ (x19_not_clob _), b₁]
  rw [WP.block_append_iff]
  refine WP.mono (bitMask_bool_ok hs₃ hx19₃ (by have := hL.bits; omega) hA.bits hbyte)
    fun s₄ ⟨c₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (sel_ok (e.testBit (j - 1)) P.M.n hs₄ c₄ hacc hacc htmp hA.acc hA.acc hA.tmp
    (Or.inl (Nat.le_refl _)) (by omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hx19₅ : s₅.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), hx19₃]
  have hm₄ : s₄.mem = s₃.mem := k₄.mem
  refine ⟨⟨hs₄.of_keepRegs k₅ (by decide), hx19₅, ?_, ?_, ?_, ?_⟩, hx19₅⟩
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · have hr' : r ∉ clob P.M.n := fun h => hr (List.mem_cons_of_mem _ h)
      have hrb : r ≠ .x19 := fun h => hr (h ▸ List.mem_cons_self ..)
      have hrc := not_mem_of_clob hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrc
      rw [k₅.gpr r (by simp [hrc.1.1, hrc.1.2.1]), k₄.gpr r (by simp [hrc.1.1, hrc.1.2.2.1,
          hrc.1.2.2.2.2.2.2.1, hrc.1.2.2.2.2.2.2.2.1]),
        k₃.gpr r hr', k₂.gpr r hr', k₁.gpr r (by simp [hrb]), hI.keep.gpr r hr]
    · rw [k₅.rd, k₄.rd, k₃.rd, k₂.rd, k₁.rd, hI.keep.rd]
    · rw [k₅.wr, k₄.wr, k₃.wr, k₂.wr, k₁.wr, hI.keep.wr]
    · rw [k₅.sp, k₄.sp, k₃.sp, k₂.sp, k₁.sp, hI.keep.sp]
  · intro x hx
    rw [O₅ x (hx _ (List.mem_cons_self ..)), hm₄]
    exact hU₃ x hx
  · rw [e₅, hm₄]
    split
    · exact lt₃
    · rw [hA₃]; exact lt₂
  · rw [e₅, hm₄, pow_shiftRight _ e (j - 1), Nat.sub_add_cancel hj, ← hI.val]
    split
    · rw [v₃, v₂]
    · rw [hA₃, v₂, Lean.Grind.Semiring.mul_one]

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e < 2^nbits`
whose bits are the table at `P.bits`; only `powClob` and `powW` change. -/
theorem pow_ok {P : PowCfg} {base : Addr} {size m e : Nat} [NeZero m] (hL : PowLay P size)
    (hA : PowA P) (hm : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOk P.M size m s.mem base) (hB : wordsVal s.mem base P.base P.M.n < m)
    (hO : wordsVal s.mem base P.one P.M.n = 2 ^ (64 * P.M.n) % m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    (he : e < 2 ^ P.nbits) :
    WP isa (pow P) s fun s' => KeepRegs (powClob P.M.n) s s' ∧ Unch base (powW P) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e := by
  have hn := hs.nowrap
  have hnb := hL.nbits
  have hm0 : 0 < m := m_pos hB
  rw [pow]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok P.M.n hs hL.acc hL.one hA.acc hA.one (by have := hL.acc_one; omega))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  refine WP.mono (setCounter_ok s₁ hnb.2) fun s₂ ⟨b₂, k₂⟩ => ?_
  refine countLoop_ok (Inv := fun j s' => PowInv P base size m e s s' j) (n := P.nbits) (by omega)
    (fun j s' h1 h2 hi => powBody_ok hL hA hm hM hB hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, by rw [hi.val, Nat.shiftRight_zero]⟩) hnb.1 ?_
  have hm₂ : s₂.mem = s₁.mem := k₂.mem
  refine ⟨(hs.of_keepRegs k₁ (by decide)).of_keeps k₂ (by decide), b₂, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [k₂.rd, k₁.rd], by rw [k₂.wr, k₁.wr], by rw [k₂.sp, k₁.sp]⟩
    have hra : r ≠ .x1 := fun h => hr (h ▸ by simp [powClob, clob])
    rw [k₂.gpr r (fun h => hr (by simp at h; simp [h, powClob])), k₁.gpr r (by simp [hra])]
  · rw [hm₂]; exact O₁.unch.mono fun w hw => by simp at hw; simp [hw, powW]
  · rw [hm₂, e₁, hO]; exact Nat.mod_lt _ hm0
  · rw [hm₂, e₁, hO, toM_one hm, shiftRight_eq_zero he, Lean.Grind.Semiring.pow_zero]

end VG.Proof.Weierstrass.AArch64
