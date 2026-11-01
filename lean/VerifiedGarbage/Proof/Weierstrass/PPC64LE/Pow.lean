module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Short Weierstrass curves on PPC64LE: powers

`pow P S` leaves `[acc]` reading (in Montgomery form) as `[base]^e`, for
the exponent `e` whose bits are the table at `P.bits` (`pow_ok`): an
iteration squares the accumulator, multiplies it by the base into `[tmp]`
and keeps that product if the exponent's bit is set (`powBody_ok`), by
calls of the functions of `S`, as on 32-bit ARM
(`Proof/Weierstrass/Arm/Pow.lean`). The functions hold their own copy of the
modulus, in their own working space, which is above the power's slots and
below its table (`PowLayP`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
  VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass
  VG.Proof.Weierstrass.PPC64LE.Mont

/-- The registers a power or the ladder changes. -/
def powClob : List Reg := .r31 :: fnClob

/-- What a power writes, for numbers of `k` words: the accumulator, the
temporary and the functions' own working space. -/
def powWx (P : PowCfg) (k : Nat) : List (Nat × Nat) :=
  [(P.acc, 8 * k), (P.tmp, 8 * k), (own k, 64 * k)]

/-- Where a power's slots and table are, for numbers of `k` words: the slots
below the functions' own working space, at multiples of 4, the table above it
in the working space, and what it reads apart from what it writes. -/
structure PowLayP (P : PowCfg) (k : Nat) : Prop where
  acc : P.acc + 8 * k ≤ own k
  tmp : P.tmp + 8 * k ≤ own k
  base : P.base + 8 * k ≤ own k
  one : P.one + 8 * k ≤ own k
  own : own k + 64 * k ≤ P.bits
  bits : P.bits + P.nbits ≤ 8192
  nbits : 1 ≤ P.nbits ∧ P.nbits < 2 ^ 15
  acc_tmp : P.acc + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.acc
  acc_one : P.acc + 8 * k ≤ P.one ∨ P.one + 8 * k ≤ P.acc
  base_acc : P.base + 8 * k ≤ P.acc ∨ P.acc + 8 * k ≤ P.base
  base_tmp : P.base + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.base
  acc4 : P.acc % 4 = 0
  tmp4 : P.tmp % 4 = 0
  one4 : P.one % 4 = 0

/-- The loop's invariant at `r31 = j`: the accumulator reads as
`B^(e >>> j)`, for `B` what the base reads as at the start. -/
structure PowInv (P : PowCfg) (k : Nat) (base : Addr) (m e : Nat) [NeZero m] (s₀ s : State)
    (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (powWx P k) s₀.mem s.mem
  lt : wordsVal s.mem base P.acc k < m
  val : toM m (2 ^ (64 * k)) (wordsVal s.mem base P.acc k) =
    toM m (2 ^ (64 * k)) (wordsVal s₀.mem base P.base k) ^ (e >>> j)

/-- An iteration. -/
theorem powBody_ok {P : PowCfg} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m)
    (hk : P.M.n = S.k) (hL : PowLayP P S.k) (hm : UnitMod S.m (2 ^ (64 * S.k))) {base : Addr} {e : Nat}
    {s₀ : State} (hB : wordsVal s₀.mem base P.base S.k < S.m)
    (hbits : ∀ t < P.nbits, s₀.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ P.nbits) (hI : PowInv P S.k base S.m e s₀ s j) :
    WP isa (powBody P S) s fun s' => PowInv P S.k base S.m e s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have := hL.acc; have := hL.tmp; have := hL.base; have := hL.own; have := hL.bits
  have hat := hL.acc_tmp
  have hba := hL.base_acc
  have hbt := hL.base_tmp
  have hBs : wordsVal s.mem base P.base S.k = wordsVal s₀.mem base P.base S.k :=
    hI.unch.wordsVal (fun w hw => by
      simp only [powWx, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hba
      · exact hbt
      · exact .inl hL.base) (by omega)
  -- `r31 -= 1` and `acc = acc²`.
  rw [powBody]
  refine WP.seq (wp_decCounter hj hI.r31 (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have w₁ := hI.ws.of_rk (K₁.rk (rs' := powClob))
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  refine WP.seq (WP.mono (mulCall_ok hM w₁ hL.acc hL.acc hL.acc (by rw [m₁]; exact hI.lt))
    fun s₂ ⟨K₂, lt₂, e₂⟩ => ?_)
  have v₂ : toM S.m (2 ^ (64 * S.k)) (wordsVal s₂.mem base P.acc S.k) =
      toM S.m (2 ^ (64 * S.k)) (wordsVal s.mem base P.acc S.k) ^ 2 := by
    rw [toM_mul hm e₂, m₁, Lean.Grind.Semiring.pow_two]
  have U₂ : Unch base [(P.acc, 8 * S.k), (own S.k, 64 * S.k)] s.mem s₂.mem := by rw [← m₁]; exact K₂.mem
  have hB₂ : wordsVal s₂.mem base P.base S.k = wordsVal s₀.mem base P.base S.k := by
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hba
      · exact .inl hL.base) (by omega), hBs]
  -- `tmp = acc · base`.
  have w₂ := w₁.of_rk (K₂.rk (rs := powClob))
  refine WP.seq (WP.mono (mulCall_ok hM w₂ hL.tmp hL.acc hL.base (by rw [hB₂]; exact hB))
    fun s₃ ⟨K₃, lt₃, e₃⟩ => ?_)
  have U₃ : Unch base [(P.tmp, 8 * S.k), (own S.k, 64 * S.k)] s₂.mem s₃.mem := K₃.mem
  have hA₃ : wordsVal s₃.mem base P.acc S.k = wordsVal s₂.mem base P.acc S.k :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact .inl hL.acc) (by omega)
  have v₃ : toM S.m (2 ^ (64 * S.k)) (wordsVal s₃.mem base P.tmp S.k) =
      toM S.m (2 ^ (64 * S.k)) (wordsVal s₂.mem base P.acc S.k) *
        toM S.m (2 ^ (64 * S.k)) (wordsVal s₀.mem base P.base S.k) := by
    rw [toM_mul hm e₃, hB₂]
  -- The mask of bit `j - 1`, and the selection.
  have hU₃ : Unch base (powWx P S.k) s₀.mem s₃.mem := by
    refine ((hI.unch.trans U₂).trans U₃).mono fun w hw => ?_
    simp only [powWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ((h | h | h) | h | h) | h | h <;> simp [h]
  have hbyte : s₃.mem (off base (P.bits + (j - 1))) = if e.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (fun w hw => by
      simp only [powWx, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> (simp only; omega)) (by omega), hbits _ (by omega)]
  have w₃ := w₂.of_rk (K₃.rk (rs := powClob))
  have c₃ : s₃.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [K₃.gpr _ (by decide), K₂.gpr _ (by decide), c₁]
  refine wp_append (WP.mono (bitMask_bool_ok w₃.ws w₃.at3 c₃ (by omega) hbyte) fun s₄ ⟨g₄, k₄, m₄⟩ => ?_)
  rw [hk]
  refine WP.mono (sel_ok (e.testBit (j - 1)) S.k (k₄.ws w₃.ws) (k₄.at w₃.at3) g₄ (o := P.acc) (a := P.acc)
    (b := P.tmp) hL.acc4 hL.acc4 hL.tmp4 (by omega) (by omega) (by omega) (Or.inl (Nat.le_refl _))
    (by omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have k₅' : Rk powClob s₃ s₅ := (k₄.rk (rs' := powClob)).trans (k₅.rk (rs' := powClob))
  refine ⟨w₃.of_rk k₅', by rw [k₅.g, k₄.g, c₃],
    (((hI.keep.trans (K₁.rk (rs' := powClob))).trans (K₂.rk (rs := powClob))).trans (K₃.rk (rs := powClob))).trans
      k₅', fun x hx => ?_, ?_, ?_⟩
  · rw [O₅ x (hx _ (List.mem_cons_self ..)), m₄]
    exact hU₃ x hx
  · rw [e₅, m₄]
    split
    · exact lt₃
    · rw [hA₃]; exact lt₂
  · rw [e₅, m₄, pow_shiftRight _ e (j - 1), Nat.sub_add_cancel hj, ← hI.val]
    split
    · rw [v₃, v₂]
    · rw [hA₃, v₂, Lean.Grind.Semiring.mul_one]

/-- `pow_ok`, for the modulus's own numbers. -/
theorem pow_ok' {P : PowCfg} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m)
    (hk : P.M.n = S.k) (hL : PowLayP P S.k) (hm : UnitMod S.m (2 ^ (64 * S.k))) {base : Addr} {e : Nat}
    {s : State} (hs : WsReg s base) (hB : wordsVal s.mem base P.base S.k < S.m)
    (hO : wordsVal s.mem base P.one S.k = 2 ^ (64 * S.k) % S.m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    (he : e < 2 ^ P.nbits) :
    WP isa (pow P S) s fun s' => Rk powClob s s' ∧ Unch base (powWx P S.k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc S.k < S.m ∧
      toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem base P.acc S.k) =
        toM S.m (2 ^ (64 * S.k)) (wordsVal s.mem base P.base S.k) ^ e := by
  have hn := hs.nowrap
  have hnb := hL.nbits
  have hm0 : 0 < S.m := m_pos hB
  have := hL.acc; have := hL.one; have := hL.own; have := hL.bits
  have hao := hL.acc_one
  rw [pow, hk]
  refine WP.seq (wp_append (WP.mono (copy_ok S.k hs.ws hs.at3 (o := P.acc) (a := P.one) hL.acc4 hL.one4
    (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ =>
      wp_step (exec_li hnb.2) (WP.block_nil ?_)))
  refine countLoop_ok (Inv := fun j s' => PowInv P S.k base S.m e s s' j) (n := P.nbits)
    (fun j s' hi => hi.r31) (fun j s' h1 h2 hi => powBody_ok hM hk hL hm hB hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, by rw [hi.val, Nat.shiftRight_zero]⟩) hnb.1 (by omega) ?_
  have hv : wordsVal (s₁.write .r31 (BitVec.ofNat 64 P.nbits)).mem base P.acc S.k =
      wordsVal s.mem base P.one S.k := by
    rw [write_mem, e₁]
  have K : Kp powClob s (s₁.write .r31 (BitVec.ofNat 64 P.nbits)) :=
    (k₁.mono (by decide)).trans (Kp.write _ _ (by decide))
  refine ⟨hs.of_rk (K.rk (rs' := powClob)), by simp only [write_gpr, ite_true], K.rk, ?_, ?_, ?_⟩
  · rw [write_mem]
    exact O₁.unch.mono fun w hw => by simp at hw; simp [hw, powWx]
  · rw [hv, hO]; exact Nat.mod_lt _ hm0
  · rw [hv, hO, toM_one hm, shiftRight_eq_zero he, Lean.Grind.Semiring.pow_zero]

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e < 2^nbits`
whose bits are the table at `P.bits`, modulo `m` on numbers of `k` words
(the functions' `S.m` and `S.k`); only `powClob` and `powWx` change. -/
theorem pow_ok {P : PowCfg} {S : Impl.Weierstrass.Mont.Modulus} {k m : Nat} [NeZero m] (hkS : S.k = k)
    (hmS : S.m = m) (hM : ModOk k m) (hk : P.M.n = k) (hL : PowLayP P k) (hm : UnitMod m (2 ^ (64 * k)))
    {base : Addr} {e : Nat} {s : State} (hs : WsReg s base) (hB : wordsVal s.mem base P.base k < m)
    (hO : wordsVal s.mem base P.one k = 2 ^ (64 * k) % m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    (he : e < 2 ^ P.nbits) :
    WP isa (pow P S) s fun s' => Rk powClob s s' ∧ Unch base (powWx P k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc k < m ∧
      toM m (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) =
        toM m (2 ^ (64 * k)) (wordsVal s.mem base P.base k) ^ e := by
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  exact pow_ok' (S := ⟨cv, w, m', k', d⟩) hM hk hL hm hs hB hO hbits he

end VG.Proof.Weierstrass.PPC64LE
