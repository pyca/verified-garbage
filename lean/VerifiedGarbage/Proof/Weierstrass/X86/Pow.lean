import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.Pow

/-!
# Short Weierstrass curves on x86 (32-bit): powers

`pow P wk` leaves `[acc]` reading (in Montgomery form) as `[base]^e`, for
the exponent `e` whose bits are the table at `P.bits` (`pow_ok`): an
iteration squares the accumulator, multiplies it by the base into `[tmp]`
and keeps that product if the exponent's bit is set (`powBody_ok`). The
multiplications' accumulator at `wk` is above everything the power uses
(`PowWk`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- The registers a power or the ladder changes. -/
def powClob : List Reg := .esi :: clob

theorem esi_not_clob : Reg.esi ∉ clob := by decide

/-- What a power writes: `powW` and the multiplications' accumulator. -/
def powWx (P : PowCfg) (wk : Nat) : List (Nat × Nat) := powW P ++ [(wk, accLen P.M)]

/-- The multiplications' accumulator at `wk`, in the working space above a
power's slots, modulus and table; and the power's temporary apart from the
modulus's. -/
structure PowWk (P : PowCfg) (size wk : Nat) : Prop where
  le : wk + accLen P.M ≤ size
  acc : P.acc + 8 * P.M.n ≤ wk
  tmp : P.tmp + 8 * P.M.n ≤ wk
  base : P.base + 8 * P.M.n ≤ wk
  mo : P.M.mo + 8 * P.M.n ≤ wk
  mtmp : P.M.tmp + 8 * P.M.n ≤ wk
  bits : P.bits + P.nbits ≤ wk
  tmp_mtmp : P.tmp + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.tmp

/-- The loop's invariant at `esi = j`: the accumulator reads as
`B^(e >>> j)`, for `B` what the base reads as at the start. -/
structure PowInv (P : PowCfg) (wk : Nat) (base : Addr) (size m e : Nat) [NeZero m] (s₀ s : State)
    (j : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 j
  keep : Keeps powClob s₀ s
  unch : Unch base (powWx P wk) s₀.mem s.mem
  lt : wordsVal s.mem base P.acc P.M.n < m
  val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) =
    toM m (2 ^ (64 * P.M.n)) (wordsVal s₀.mem base P.base P.M.n) ^ (e >>> j)

/-- An iteration. -/
theorem powBody_ok {P : PowCfg} {wk : Nat} {base : Addr} {size m e : Nat} [NeZero m] (hL : PowLay P size)
    (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n))) {s₀ : State}
    (hM₀ : ModOk P.M size m s₀.mem base) (hB : wordsVal s₀.mem base P.base P.M.n < m)
    (hbits : ∀ t < P.nbits, s₀.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ P.nbits) (hI : PowInv P wk base size m e s₀ s j) :
    WP isa (powBody P wk) s fun s' =>
      PowInv P wk base size m e s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hn := hI.scr.nowrap
  have hnb := hL.nbits
  have hacc := hL.acc
  have htmp := hL.tmp
  have hat := hL.acc_tmp
  have ham := hL.acc_mtmp
  have hmo' := hM₀.mo
  have hbase := hL.base
  have hbl := hL.bits
  have := hW.le; have := hW.acc; have := hW.tmp; have := hW.base; have := hW.mo; have := hW.mtmp
  have := hW.bits
  have hmo : ∀ w ∈ powWx P wk, P.M.mo + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.M.mo := by
    intro w hw
    simp only [powWx, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hL.mo_w w hw
    · exact .inl hW.mo
  have hbw : ∀ w ∈ powWx P wk, P.base + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.base := by
    intro w hw
    simp only [powWx, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hL.base_w w hw
    · exact .inl hW.base
  have hM : ModOk P.M size m s.mem base :=
    ⟨hM₀.n0, hM₀.n7, hM₀.mo, hM₀.tmp, hM₀.sep,
      by rw [hI.unch.wordsVal hmo (by omega)]; exact hM₀.val, hM₀.inv, hM₀.red⟩
  have hBs : wordsVal s.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n :=
    hI.unch.wordsVal hbw (by omega)
  have hlay : ∀ {o a b : Nat}, o + 8 * P.M.n ≤ wk → a + 8 * P.M.n ≤ wk → b + 8 * P.M.n ≤ wk →
      o + 8 * P.M.n ≤ size → a + 8 * P.M.n ≤ size → b + 8 * P.M.n ≤ size →
      (o + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ o) → OpLay P.M size wk o a b :=
    fun h1 h2 h3 h4 h5 h6 h7 => ⟨hW.le, h4, h5, h6, .inr h1, .inr h2, .inr h3, .inr hW.mo, .inr hW.mtmp, h7⟩
  -- `esi -= 1` and `acc = acc²`.
  rw [powBody]
  refine WP.seq (wp_decCounter hj hI.esi fun s₁ b₁ k₁ hm₁ => WP.block_nil ?_)
  have hs₁ := hI.scr.of_keeps k₁ (by decide)
  refine WP.seq (WP.mono (mul_ok hs₁ (hm₁ ▸ hM) (hlay hW.acc hW.acc hW.acc hacc hacc hacc ham)
    (by rw [hm₁]; exact hI.lt)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have hU₂ := k₂.unch
  have hM₂ : ModOk P.M size m s₂.mem base :=
    ⟨hM.n0, hM.n7, hM.mo, hM.tmp, hM.sep, by
      rw [hU₂.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact hmo _ (by simp [powWx, powW])
        · exact hmo _ (by simp [powWx, powW])
        · exact hmo _ (by simp [powWx])) (by omega), hm₁]; exact hM.val, hM.inv, hM.red⟩
  have v₂ : toM m (2 ^ (64 * P.M.n)) (wordsVal s₂.mem base P.acc P.M.n) =
      toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) ^ 2 := by
    rw [toM_mul hm (e₂.trans (by rw [hm₁])), Lean.Grind.Semiring.pow_two]
  have hB₂ : wordsVal s₂.mem base P.base P.M.n = wordsVal s₀.mem base P.base P.M.n := by
    rw [hU₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hbw _ (by simp [powWx, powW])
      · exact hbw _ (by simp [powWx, powW])
      · exact hbw _ (by simp [powWx])) (by omega), hm₁, hBs]
  -- `tmp = acc · base`.
  refine WP.seq (WP.mono (mul_ok hs₂ hM₂ (hlay hW.tmp hW.acc hW.base htmp hacc hbase hW.tmp_mtmp)
    (by rw [hB₂]; exact hB)) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have hA₃ : wordsVal s₃.mem base P.acc P.M.n = wordsVal s₂.mem base P.acc P.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hat
      · exact ham
      · exact .inl hW.acc) (by omega)
  have v₃ : toM m (2 ^ (64 * P.M.n)) (wordsVal s₃.mem base P.tmp P.M.n) =
      toM m (2 ^ (64 * P.M.n)) (wordsVal s₂.mem base P.acc P.M.n) *
        toM m (2 ^ (64 * P.M.n)) (wordsVal s₀.mem base P.base P.M.n) := by
    rw [toM_mul hm e₃, hB₂]
  -- The mask of bit `j - 1`, and the selection.
  have hU₃ : Unch base (powWx P wk) s₀.mem s₃.mem := by
    refine ((hI.unch.trans (by rw [← hm₁]; exact hU₂)).trans k₃.unch).mono fun w hw => ?_
    simp only [powWx, powW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  have hbyte : s₃.mem (off base (P.bits + (j - 1))) = if e.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (fun w hw => by
      simp only [powWx, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have := hL.bits_w w hw; omega
      · simp only; omega) (by omega), hbits _ (by omega)]
  have hesi₃ : s₃.gpr .esi = BitVec.ofNat 32 (j - 1) := by
    rw [k₃.gpr _ esi_not_clob, k₂.gpr _ esi_not_clob, b₁]
  have hk₃ : Keeps powClob s₀ s₃ :=
    (hI.keep.widen k₁) |>.trans ⟨fun r hr => by
      rw [k₃.gpr r (fun h => hr (List.mem_cons_of_mem _ h)), k₂.gpr r (fun h => hr (List.mem_cons_of_mem _ h))],
      by rw [k₃.rd, k₂.rd], by rw [k₃.wr, k₂.wr]⟩
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (bitMask_bool_ok hs₃ hesi₃ (by omega) hbyte) fun s₄ ⟨c₄, k₄, hm₄⟩ => ?_)
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.block_append (WP.mono (sel_ok (e.testBit (j - 1)) (2 * P.M.n) hs₄ c₄ (o := P.acc) (a := P.acc)
    (b := P.tmp) (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _)) (by omega))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  have hesi₅ : s₅.gpr .esi = BitVec.ofNat 32 (j - 1) := by
    rw [k₅.1 _ (by decide), k₄.1 _ (by decide), hesi₃]
  refine wp_testCounter (by omega) hesi₅ fun s₆ f₆ z₆ => WP.block_nil ⟨⟨hs₄.of_keeps (k₅.trans (f₆.keeps _))
    (by decide), by rw [f₆.gpr, hesi₅], (hk₃.widen k₄).widen (k₅.trans (f₆.keeps _)), ?_, ?_, ?_⟩, z₆⟩
  · intro x hx
    rw [f₆.mem, O₅ x (by rw [show 4 * (2 * P.M.n) = 8 * P.M.n by omega]; exact hx _ (List.mem_cons_self ..)),
      hm₄]
    exact hU₃ x hx
  · rw [f₆.mem, wordsVal_eq_val32, e₅, hm₄, ← wordsVal_eq_val32, ← wordsVal_eq_val32]
    split
    · exact lt₃
    · rw [hA₃]; exact lt₂
  · rw [f₆.mem, wordsVal_eq_val32, e₅, hm₄, ← wordsVal_eq_val32, ← wordsVal_eq_val32,
      pow_shiftRight _ e (j - 1), Nat.sub_add_cancel hj, ← hI.val]
    split
    · rw [v₃, v₂]
    · rw [hA₃, v₂, Lean.Grind.Semiring.mul_one]

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e < 2^nbits`
whose bits are the table at `P.bits`; only `powClob` and `powWx` change. -/
theorem pow_ok {P : PowCfg} {wk : Nat} {base : Addr} {size m e : Nat} [NeZero m] (hL : PowLay P size)
    (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOk P.M size m s.mem base) (hB : wordsVal s.mem base P.base P.M.n < m)
    (hO : wordsVal s.mem base P.one P.M.n = 2 ^ (64 * P.M.n) % m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    (he : e < 2 ^ P.nbits) :
    WP isa (pow P wk) s fun s' => Keeps powClob s s' ∧ Unch base (powWx P wk) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal s'.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ e := by
  have hn := hs.nowrap
  have hnb := hL.nbits
  have hm0 : 0 < m := m_pos hB
  have hacc := hL.acc
  have hone := hL.one
  rw [pow]
  refine WP.seq (WP.block_append (WP.mono (copy_ok (2 * P.M.n) hs (o := P.acc) (a := P.one) (by omega)
    (by omega) (by have := hL.acc_one; omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_))
  refine wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_
  refine countLoop_ok (Inv := fun j s' => PowInv P wk base size m e s s' j) (n := P.nbits)
    (fun j s' h1 h2 hi => powBody_ok hL hW hm hM hB hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, by rw [hi.val, Nat.shiftRight_zero]⟩) hnb.1 ?_
  have hm₂ : s₂.mem = s₁.mem := u₂.mem
  have hv : wordsVal s₂.mem base P.acc P.M.n = wordsVal s.mem base P.one P.M.n := by
    rw [hm₂, wordsVal_eq_val32, e₁, ← wordsVal_eq_val32]
  refine ⟨(hs.of_keeps k₁ (by decide)).of_keeps u₂.keeps (by decide), u₂.gpr,
    (k₁.mono (by decide)).widen u₂.keeps, ?_, ?_, ?_⟩
  · rw [hm₂]
    rw [show 4 * (2 * P.M.n) = 8 * P.M.n by omega] at O₁
    exact O₁.unch.mono fun w hw => by simp at hw; simp [hw, powWx, powW]
  · rw [hv, hO]; exact Nat.mod_lt _ hm0
  · rw [hv, hO, toM_one hm, shiftRight_eq_zero he, Lean.Grind.Semiring.pow_zero]

end VG.Proof.Weierstrass.X86
