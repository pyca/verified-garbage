module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.TCombI
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Ladder
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Fprog
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderPCall
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.CombPointW
import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step

/-!
# The comb's `[k]G` with the addition inlined, on PPC64LE

`combI` (`Impl/Weierstrass/PPC64LE/TCombI.lean`), for coordinates of more
than 6 words, on the ladder's layout (`LadLayI`): the comb's window, digit,
scan and sign (`Proof/Weierstrass/PPC64LE/TComb.lean`), the entry selected
to the ladder's `T`, and `R = R + T` by the complete addition inlined into
`D` (`rcb_ok`), then copied to `R`. `combI_ok`: `R = [k]G`, reduced, with
only the registers of `powClob` and the ladder's writes (`ladWx`) changed.
-/

-- separate module: the comb of the curves of more than 6 words, which each one's configuration imports

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.TComb

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.PPC64LE.Mont (own)
open Spec.Weierstrass

/-! ## The layout -/

/-- The ladder's layout, the entry selected to its `T` (contiguous), `-y`
in `D`'s `x`, zero in a slot the ladder does not write, and the addition's
slots apart. -/
structure LayoutI (K : TCombCfg) : Prop where
  lad : LadLayI K.L
  bitsE : K.L.bits + K.L.nbits ≤ 8192
  wx : ∀ w ∈ ladWx K.L, w.1 + w.2 ≤ 4096
  qT : K.Q = K.L.T
  qy : K.L.T.y = K.L.T.x + 8 * K.L.M.n
  qz : K.L.T.z = K.L.T.x + 16 * K.L.M.n
  negD : K.neg = K.L.D.x
  zeroLe : K.zero + 8 * K.L.M.n ≤ own K.L.M.n
  zero4 : K.zero % 4 = 0
  zeroW : ∀ w ∈ ladWx K.L, K.zero + 8 * K.L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.zero
  apart : RcbApart K.L.S K.L.R K.L.T K.L.D

/-- The ladder's layout with another number of bits in its table. -/
theorem _root_.VG.Proof.Weierstrass.PPC64LE.Point.LadLayI.with_nbits {L : LadderCfg} (h : LadLayI L) {nb : Nat} (h1 : 1 ≤ nb) (h15 : nb < 2 ^ 15)
    (hb : L.bits + nb ≤ 8192) (hw : ∀ w ∈ ladW L, L.bits + nb ≤ w.1 ∨ w.1 + w.2 ≤ L.bits) :
    LadLayI { L with nbits := nb } :=
  ⟨⟨h.lay.lay, h.lay.a1, h.lay.a2, h.lay.ro, h.lay.rne, h.lay.rdt, ⟨h1, show nb < 2 ^ 16 by omega⟩, hb, hw⟩, h.al, h.bits, h15⟩

theorem mem_ladWx {L : LadderCfg} {x : Nat} (h : x ∈ ladWs L) : (x, 8 * L.M.n) ∈ ladWx L := by
  simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton]
  exact .inl (.inl ⟨x, h, rfl⟩)

theorem own_ladWx (L : LadderCfg) : (own L.M.n, 64 * L.M.n) ∈ ladWx L := by
  simp [ladWx]

/-- The numbers of the slots the entry uses. -/
theorem LayoutI.nums {K : TCombCfg} (h : LayoutI K) :
    own K.L.M.n + 64 * K.L.M.n = 4096 ∧
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.Q.x, K.Q.y, K.Q.z, K.neg, K.zero, K.L.S.a, K.L.S.b3],
      x + 8 * K.L.M.n ≤ own K.L.M.n ∧ x % 4 = 0) ∧
    K.Q.y = K.Q.x + 8 * K.L.M.n ∧ K.Q.z = K.Q.x + 16 * K.L.M.n ∧
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.zero, K.neg], x + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ x) ∧
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.zero], K.neg + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.neg) ∧
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], K.zero + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.zero) := by
  have hL := h.lad
  have sl : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.L.T.x, K.L.T.y, K.L.T.z, K.L.D.x, K.L.S.a,
      K.L.S.b3], x ∈ ladSlots K.L := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ladPts_slots K.L _ ?_; simp; done)
      | (refine ladR_slots K.L _ ?_; simp [ladR, ladRo]; done)
  have ap : ∀ {x y}, x ∈ ladSlots K.L → y ∈ ladSlots K.L → x ≠ y →
      x + 8 * K.L.M.n ≤ y ∨ y + 8 * K.L.M.n ≤ x := fun hx hy hne => hL.lay.lay.apart _ _ hx hy hne
  have le : ∀ {x}, x ∈ ladSlots K.L → x + 8 * K.L.M.n ≤ own K.L.M.n := fun hx => hL.lay.lay.le _ hx
  have hR := le (sl K.L.R.x (by simp))
  have hown := own_add K.L.M.n (by omega)
  have qx : K.Q.x = K.L.T.x := by rw [h.qT]
  have qy : K.Q.y = K.L.T.y := by rw [h.qT]
  have qz : K.Q.z = K.L.T.z := by rw [h.qT]
  have hqy := h.qy
  have hqz := h.qz
  have nd := h.negD
  -- what differs from what
  have rT : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], ∀ y ∈ [K.L.T.x, K.L.T.y, K.L.T.z, K.L.D.x], x ≠ y :=
    fun x hx y hy e => hL.lay.rdt x hx (by
      subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with h | h | h | h <;> simp [h])
  have zA : ∀ y ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.L.T.x, K.L.T.y, K.L.T.z, K.L.D.x],
      K.zero + 8 * K.L.M.n ≤ y ∨ y + 8 * K.L.M.n ≤ K.zero :=
    fun y hy => h.zeroW _ (mem_ladWx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with h | h | h | h | h | h | h <;> rw [h] <;> mem_list))
  have tD : ∀ y ∈ [K.L.T.x, K.L.T.y, K.L.T.z], y ≠ K.L.D.x := fun y hy e =>
    h.apart.apart y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with h | h | h <;> rw [h] <;> mem_list) (by rw [e]; mem_list)
  refine ⟨hown, ?_, by rw [qy, qx, hqy], by rw [qz, qx, hqz], ?_, ?_, ?_⟩
  · intro x hx
    rw [qx, qy, qz, nd] at hx
    by_cases hz : x = K.zero
    · subst hz; exact ⟨h.zeroLe, h.zero4⟩
    exact ⟨le (sl x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega)),
      hL.al x (sl x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega))⟩
  · have tx := sl K.L.T.x (by simp)
    have ty := sl K.L.T.y (by simp)
    have tz := sl K.L.T.z (by simp)
    have apT : ∀ {x}, x ∈ ladSlots K.L → x ≠ K.L.T.x → x ≠ K.L.T.y → x ≠ K.L.T.z →
        x + 8 * K.L.M.n ≤ K.L.T.x ∨ K.L.T.x + 24 * K.L.M.n ≤ x := fun hx a b c => by
      have := ap hx tx a; have := ap hx ty b; have := ap hx tz c; omega
    intro x hx
    rw [qx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact apT (sl _ (by simp)) (rT _ (by simp) _ (by simp)) (rT _ (by simp) _ (by simp))
        (rT _ (by simp) _ (by simp))
    · exact apT (sl _ (by simp)) (rT _ (by simp) _ (by simp)) (rT _ (by simp) _ (by simp))
        (rT _ (by simp) _ (by simp))
    · exact apT (sl _ (by simp)) (rT _ (by simp) _ (by simp)) (rT _ (by simp) _ (by simp))
        (rT _ (by simp) _ (by simp))
    · have := zA K.L.T.x (by simp); have := zA K.L.T.y (by simp); have := zA K.L.T.z (by simp); omega
    · rw [nd]
      exact apT (sl _ (by simp)) (tD _ (by simp)).symm (tD _ (by simp)).symm (tD _ (by simp)).symm
  · intro x hx
    rw [nd]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ap (sl _ (by simp)) (sl _ (by simp)) (rT _ (by simp) _ (by simp)).symm
    · exact ap (sl _ (by simp)) (sl _ (by simp)) (rT _ (by simp) _ (by simp)).symm
    · exact ap (sl _ (by simp)) (sl _ (by simp)) (rT _ (by simp) _ (by simp)).symm
    · exact (zA _ (by simp)).symm
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact zA _ (by simp)

/-! ## What every iteration keeps -/

/-- What every iteration keeps: the working space, the table, zero, the
scalar's bits, and the ladder's `a` and `3b` (in Montgomery's form). -/
structure InputsI (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (base T : Addr) (k : Nat)
    (s : State) : Prop where
  wsr : WsReg s base
  table : TableMem s T (tableWords K C tbl)
  symbol : s.syms K.tsym = T
  zero : wordsVal s.mem base K.zero K.L.M.n = 0
  bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0
  coeffA : wordsVal s.mem base K.L.S.a K.L.M.n = C.a * 2 ^ (64 * K.L.M.n) % C.p
  coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n = (3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p

theorem InputsI.keep {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))} {base T : Addr} {k : Nat}
    {s t : State} {rs : List Reg} (i : InputsI K C tbl base T k s) (h : LayoutI K)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩)
    (keep : Rk rs s t) (r3 : Reg.r3 ∉ rs) (mem : Unch base (ladWx K.L) s.mem t.mem)
    (syms : t.syms = s.syms) : InputsI K C tbl base T k t := by
  obtain ⟨-, lo, -⟩ := h.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo
  obtain ⟨-, -, -, -, -, -, -, ⟨z, -⟩, ⟨a, -⟩, ⟨b, -⟩⟩ := lo
  have ho := own_lt K.L.M.n
  have nowrap := i.wsr.nowrap
  have ro : ∀ x ∈ [K.L.S.a, K.L.S.b3], ∀ w ∈ ladWx K.L, x + 8 * K.L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact h.lad.apart_wx (ladR_slots K.L _ (by simp [ladR, ladRo])) (h.lad.lay.ro _ (by simp [ladRo]))
    · exact h.lad.apart_wx (ladR_slots K.L _ (by simp [ladR, ladRo])) (h.lad.lay.ro _ (by simp [ladRo]))
  refine ⟨i.wsr.of_rk keep r3, i.table.unch (by rw [keep.rd, keep.wr]) mem
    (fun w hw => by have := h.wx w hw; omega) hd, by rw [syms]; exact i.symbol, ?_, ?_, ?_, ?_⟩
  · rw [mem.wordsVal h.zeroW (by omega), i.zero]
  · intro j hj
    rw [mem.byte (h.lad.bits_wx hj) (by have := h.bitsE; omega), i.bits j hj]
  · rw [mem.wordsVal (ro _ (by simp)) (by omega), i.coeffA]
  · rw [mem.wordsVal (ro _ (by simp)) (by omega), i.coeffB]

/-! ## The signed entry -/

/-- `y = -y` if the digit is negative: `-y` into `D`'s `x` by the field's
subtraction from zero, then the selection by the sign's mask. -/
theorem negateI_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} (positive : Prop) [Decidable positive]
    (h : LayoutI K) (hw : WsReg s base) (hm : K.F.m = m) (hn : K.F.k = K.L.M.n) (hM : ModOk K.L.M.n m)
    (hz : wordsVal s.mem base K.zero K.L.M.n = 0) (hy : wordsVal s.mem base K.Q.y K.L.M.n < m)
    (hmask : ∀ u, Rk fnClob s u → Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem u.mem →
      WP isa K.signMask u fun v =>
        v.gpr .r10 = (if positive then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r6, .r10] u v ∧ v.mem = u.mem) :
    WP isa (.seq (subCall K.F K.neg K.zero K.Q.y) (.seq K.signMask (.block (sel K.L.M.n K.Q.y K.Q.y K.neg)))) s
      fun t =>
      Rk fnClob s t ∧
      Unch base ([(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] ++ [(K.Q.y, 8 * K.L.M.n)]) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      wordsVal t.mem base K.Q.x K.L.M.n = wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n =
        (if positive then wordsVal s.mem base K.Q.y K.L.M.n else (m - wordsVal s.mem base K.Q.y K.L.M.n) % m) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = wordsVal s.mem base K.Q.z K.L.M.n := by
  obtain ⟨hown, lo, hqy, hqz, qap, nap, -⟩ := h.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo qap nap
  obtain ⟨⟨rx, -⟩, ⟨ry, -⟩, ⟨rz, -⟩, ⟨qx, qx4⟩, ⟨qy, qy4⟩, ⟨qz, -⟩, ⟨ng, ng4⟩, ⟨zr, -⟩, -, -⟩ := lo
  obtain ⟨qrx, qry, qrz, -, qng⟩ := qap
  obtain ⟨nrx, nry, nrz, -⟩ := nap
  have nowrap := hw.nowrap
  have fm : ModOk K.F.k K.F.m := by rw [hn, hm]; exact hM
  refine WP.seq (WP.mono (subCall_ok fm hw (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; omega)
    (by rw [hn, hm, hz]; exact hM.m0) (by rw [hn, hm]; exact hy)) fun u ⟨ku, yu⟩ => ?_)
  rw [hn, hm, hz, Nat.zero_add] at yu
  have ou : Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem u.mem := by
    have := ku.mem; rw [hn] at this; exact this
  have wu := hw.of_rk (ku.rk (rs := fnClob))
  refine WP.seq (WP.mono (hmask u (ku.rk) ou) fun v ⟨mask, kv, mv⟩ => ?_)
  have wv := wu.of_kp kv
  have msk : v.gpr .r10 = if decide (¬positive) then BitVec.allOnes 64 else 0 := by
    rw [mask]; by_cases hp : positive <;> simp [hp]
  refine WP.mono (sel_ok (decide (¬positive)) K.L.M.n (o := K.Q.y) (a := K.Q.y) (b := K.neg) wv.ws wv.at3 msk
    qy4 qy4 ng4 (by omega) (by omega) (by omega) (.inl (Nat.le_refl _))
    (by omega)) fun t ⟨yt, kt, ot⟩ => ?_
  have qold : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    rw [mv]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply ou.wordsVal _ (by rcases hx with rfl | rfl | rfl <;> omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by omega, .inl (by omega)⟩
  refine ⟨(ku.rk).trans ((kv.rk (by decide)).trans (kt.rk (by decide))), ?_, ?_, ?_, ?_, ?_⟩
  · have ov : Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem v.mem := by rw [mv]; exact ou
    exact ov.trans ot.unch
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have lowx : x + 8 * K.L.M.n ≤ own K.L.M.n := by rcases hx with rfl | rfl | rfl <;> assumption
    have negx : K.neg + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.neg := by
      rcases hx with rfl | rfl | rfl <;> assumption
    have qx' : x + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ x := by
      rcases hx with rfl | rfl | rfl <;> assumption
    rw [ot.wordsVal (by omega) (by omega), mv]
    apply ou.wordsVal _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨negx.symm, .inl (by omega)⟩
  · rw [ot.wordsVal (by omega) (by omega), qold _ (by simp)]
  · rw [yt, mv, yu]
    have qo := qold K.Q.y (by simp)
    rw [mv] at qo
    rw [qo]
    by_cases hp : positive <;> simp [hp]
  · rw [ot.wordsVal (by omega) (by omega), qold _ (by simp)]

/-- The side conditions of a comb with the addition inlined, which do not
depend on the scalar. -/
structure ConfigI (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (start : Nat × Nat) : Prop where
  layout : LayoutI K
  fieldK : K.F.k = K.L.M.n
  fieldM : K.F.m = C.p
  modulus : ModOk K.L.M.n C.p
  odd : C.p % 2 = 1
  unit : UnitMod C.p (2 ^ (64 * K.L.M.n))
  tables : CombOkW C K.w K.J tbl start
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.L.M.n)) K.one = 1
  startX : K.start.1 = start.1 * 2 ^ (64 * K.L.M.n) % C.p
  startY : K.start.2 = start.2 * 2 ^ (64 * K.L.M.n) % C.p
  w1 : 1 ≤ K.w
  w9 : K.w < 9
  J1 : 1 ≤ K.J
  J15 : K.J < 2 ^ 15
  startBits : K.w * (K.J - 1) ≤ K.L.nbits
  coverBits : K.L.nbits ≤ K.w * K.J
  bitsOff : K.L.bits + K.w < 2 ^ 15
  row : 16 * K.L.M.n * K.H < 2 ^ 15

theorem ConfigI.magnitude {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) (k j : Nat) : magH K.H (combWin K.w k j) ≤ K.H := by
  apply magH_le
  have pow : 2 ^ K.w = 2 * K.H := by
    change 2 ^ K.w = 2 * 2 ^ (K.w - 1)
    calc
      2 ^ K.w = 2 ^ ((K.w - 1) + 1) := congrArg (fun n => 2 ^ n) (by have := h.w1; omega)
      _ = 2 * 2 ^ (K.w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [← pow]
  exact combWin_lt _ _ _

theorem unch_three {base : Addr} {o n : Nat} {m m' : Mem} (h : Unch base [(o, 24 * n)] m m') :
    Unch base [(o, 8 * n), (o + 8 * n, 8 * n), (o + 16 * n, 8 * n)] m m' := fun x hx => h x (by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx ⊢
  omega)

/-- What the entry writes is the ladder's. -/
theorem LayoutI.entry_cover {K : TCombCfg} (h : LayoutI K) :
    ∀ w ∈ [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] ++ [(K.Q.y, 8 * K.L.M.n)] ++
      [(K.Q.x, 8 * K.L.M.n), (K.Q.x + 8 * K.L.M.n, 8 * K.L.M.n), (K.Q.x + 16 * K.L.M.n, 8 * K.L.M.n)],
      ∃ v ∈ ladWx K.L, v.1 ≤ w.1 ∧ w.1 + w.2 ≤ v.1 + v.2 := by
  have qx : K.Q.x = K.L.T.x := by rw [h.qT]
  have qy : K.Q.y = K.L.T.y := by rw [h.qT]
  have mem : ∀ x ∈ [K.L.D.x, K.L.T.x, K.L.T.y, K.L.T.z], (x, 8 * K.L.M.n) ∈ ladWx K.L := by
    intro x hx
    apply mem_ladWx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> mem_list
  intro w hw
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, mem K.L.D.x (by simp), by rw [h.negD], by rw [h.negD]⟩
  · exact ⟨_, own_ladWx K.L, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, mem K.L.T.y (by simp), by rw [qy], by rw [qy]⟩
  · exact ⟨_, mem K.L.T.x (by simp), by rw [qx], by rw [qx]⟩
  · exact ⟨_, mem K.L.T.y (by simp), by rw [qx, h.qy], by rw [qx, h.qy]⟩
  · exact ⟨_, mem K.L.T.z (by simp), by rw [qx, h.qz], by rw [qx, h.qz]⟩

/-- The entry of digit `j`, signed, in the ladder's `T`. -/
theorem entryI_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) (hC : Law C) {s : State} {base T : Addr} {k j : Nat}
    (i : InputsI K C tbl base T k s) (hj : j < K.J) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    WP isa K.entry s fun t =>
      Rk fnClob s t ∧ Unch base (ladWx K.L) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      (∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.Q.x) (tmv C K.L.M.n base t K.Q.y) (tmv C K.L.M.n base t K.Q.z)
        (signedPtW C K.w k j) := by
  unfold TCombCfg.entry
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hfit : C.p ≤ 2 ^ (64 * K.L.M.n) := Nat.le_of_lt h.modulus.m_lt
  have hn1 : 1 ≤ K.L.M.n := by
    refine Nat.pos_of_ne_zero fun e => ?_
    have := h.modulus.m_lt
    rw [e] at this
    have := h.odd
    omega
  obtain ⟨hown, lo, hqy, hqz, qap, nap, zap⟩ := h.layout.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo qap
  obtain ⟨⟨rx, -⟩, ⟨ry, -⟩, ⟨rz, -⟩, ⟨qx, hq4⟩, ⟨qy, -⟩, ⟨qz, -⟩, ⟨ng, -⟩, ⟨zr, hz4⟩, -, -⟩ := lo
  obtain ⟨qrx, qry, qrz, qzr, -⟩ := qap
  have hbits := h.layout.bitsE
  have nowrap := i.wsr.nowrap
  have hH15 : K.H + 1 ≤ 2 ^ 15 := by
    have := h.row
    have := Nat.le_mul_of_pos_left K.H (show 0 < 16 * K.L.M.n by omega)
    omega
  refine WP.seq (WP.mono_syms (digit_ok K i.wsr.ws i.wsr.at3 h.w9 hj (Nat.le_of_lt h.J15) h.startBits
    h.coverBits h.bitsOff hbits hk gj i.bits) fun u ⟨gu, ku, mu⟩ syu => ?_)
  have iu : InputsI K C tbl base T k u :=
    i.keep h.layout hd (ku.rk (rs' := fnClob)) (by decide) (by rw [mu]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (selectTable_ok K (a := magH K.H (combWin K.w k j)) iu.wsr hq4 hz4
    (by omega) (by omega) qzr (Nat.lt_of_lt_of_le h.one_lt hfit) iu.zero
    hn1 hH15 h.row (h.magnitude k j) gu
    (by rw [ku.g]; exact gj) iu.table iu.symbol h.tables.len h.tables.lenH hj (by have := h.J15; omega) hp hfit hd)
    fun v ⟨xv, yv, zv, kv, ov⟩ syv => ?_)
  have ov3 := unch_three ov.unch
  have ouv : Unch base (ladWx K.L) u.mem v.mem :=
    ov3.cover fun w hw => h.layout.entry_cover w (List.mem_append_right _ hw)
  have iv : InputsI K C tbl base T k v := iu.keep h.layout hd kv (by decide) ouv syv
  have ylt : wordsVal v.mem base K.Q.y K.L.M.n < C.p := by
    rw [yv]; split
    · exact h.one_lt
    · exact Nat.mod_lt _ hp
  have oldR : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have lowx : x + 8 * K.L.M.n ≤ own K.L.M.n := by rcases hx with rfl | rfl | rfl <;> assumption
    have qx' : x + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ x := by
      rcases hx with rfl | rfl | rfl <;> assumption
    rw [ov.unch.wordsVal (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
      (by omega), mu]
  have mask : ∀ a, Rk fnClob v a → Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] v.mem a.mem →
      WP isa K.signMask a fun b =>
        b.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r6, .r10] a b ∧
          b.mem = a.mem := by
    intro a ka ma
    have wa := iv.wsr.of_rk ka
    refine WP.mono (signMask_ok K wa.ws wa.at3 ⟨h.w1, h.w9⟩ hj (Nat.le_of_lt h.J15) h.startBits h.coverBits
      h.bitsOff hbits hk (by rw [ka.g, kv.g, ku.g]; exact gj) fun b hb => ?_) fun t ⟨v', k', m'⟩ => ⟨v', k', m'⟩
    rw [ma.byte (fun w hw' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl <;> (right; dsimp only; have := h.layout.lad.bits; omega)) (by omega),
      iv.bits b hb]
  refine WP.mono (negateI_ok K (K.H ≤ combWin K.w k j) h.layout iv.wsr h.fieldM h.fieldK h.modulus iv.zero ylt
    mask) fun t ⟨kt, ot, rt, xt, yt, zt⟩ => ?_
  refine ⟨((ku.rk (rs' := fnClob)).trans ((kv.mono (by decide)).trans kt)), ?_,
    fun x hx => (rt x hx).trans (oldR x hx), ?_, ?_⟩
  · have ou : Unch base (ladWx K.L) s.mem u.mem := by rw [mu]; exact Unch.refl _ _ _
    exact (ou.trans (ouv.trans (ot.cover fun w hw => h.layout.entry_cover w
      (List.mem_append_left _ hw)))).cover fun w hw' => ⟨w, by
        simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [xt, yt, zt, xv, zv]
    refine ⟨?_, ?_, ?_⟩
    · split
      · exact hp
      · exact Nat.mod_lt _ hp
    · split
      · exact ylt
      · exact Nat.mod_lt _ hp
    · split
      · exact hp
      · exact h.one_lt
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [xt, yt, zt]
    exact combSigned_rep hC h.tables h.unit h.one hj h.w1 xv yv zv ylt

/-! ## The addition -/

/-- `R = R + q` by the complete addition inlined into `D`, then `R = D`,
for `q` of the ladder's slots apart from what `rcb` writes. -/
theorem addI_gen {L : LadderCfg} {C : Curve} {S : Impl.Weierstrass.Mont.Modulus} {q : Pt} (hL : LadLayI L)
    (hA : RcbApart L.S L.R q L.D) (hq : ∀ x ∈ [q.x, q.y, q.z], x ∈ ladSlots L)
    (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ rcbR L.S L.R q, wordsVal s.mem base x L.M.n < C.p) :
    WP isa (.seq (fprog S (rcb L.S L.R q L.D)) (.block (copyPt L.M.n L.R L.D))) s fun t =>
      Rk fnClob s t ∧ Unch base (ladWx L) s.mem t.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal t.mem base x L.M.n < C.p) ∧
      (tmv C L.M.n base t L.R.x, tmv C L.M.n base t L.R.y, tmv C L.M.n base t L.R.z) =
        VG.Proof.Weierstrass.rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3)
          (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)
          (tmv C L.M.n base s q.x) (tmv C L.M.n base s q.y) (tmv C L.M.n base s q.z) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS hM ⊢
  subst hkS hmS
  have hSl : ∀ x ∈ rcbW L.S L.D ++ rcbR L.S L.R q, x ∈ ladSlots L := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ladWs_slots L x (by simp only [ladWs, List.mem_append]; exact .inl (.inr hx))
    · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ladR_slots L _ (by simp [ladR, ladRo])
      · exact ladR_slots L _ (by simp [ladR, ladRo])
      · exact ladPts_slots L _ (by simp)
      · exact ladPts_slots L _ (by simp)
      · exact ladPts_slots L _ (by simp)
      · exact hq _ (by simp)
      · exact hq _ (by simp)
      · exact hq _ (by simp)
  have I₀ : Inv L.M.n base C.p (· ∈ ladSlots L) (rcbR L.S L.R q) (tmv C L.M.n base s) s :=
    ⟨hw, fun x hx => hSl x (List.mem_append_right _ hx), hlt, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (rcb_ok (S' := ⟨c, w, C.p, L.M.n, d⟩) hM rfl hL.lay.lay hp hA hSl I₀ (fun x hx => hx))
    fun s₂ ⟨k₂, I₂, t₂, _⟩ => ?_)
  have hn := hw.nowrap
  have ho := own_add L.M.n (by have := hL.lay.lay.le _ (ladPts_slots L L.R.x (by simp)); omega)
  have pts := ladPts_slots L
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.lay.apart x y (pts x hx) (pts y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.lay.rne
  have rD : ∀ d ∈ [L.R.x, L.R.y, L.R.z], ∀ e ∈ [L.D.x, L.D.y, L.D.z], d + 8 * L.M.n ≤ e ∨ e + 8 * L.M.n ≤ d :=
    fun d hd e he => hap d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with h | h | h <;> simp [h]) e
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢; rcases he with h | h | h <;> simp [h])
      fun h' => hL.lay.rdt d hd (by
        subst h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
        rcases he with h | h | h <;> simp [h])
  refine WP.mono (copyPt_ok I₂.ws.ws I₂.ws.at3 (n := L.M.n) (o := L.R) (a := L.D)
    (fun d hd => hL.al d (pts d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      rcases hd with h | h | h | h | h | h <;> simp [h])))
    (fun d hd => by
      have := hL.lay.lay.le d (pts d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
        rcases hd with h | h | h | h | h | h <;> simp [h]))
      omega)
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩ rD)
    fun t ⟨ex, ey, ez, kt, ot⟩ => ?_
  have dW : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.D ++ rcbR L.S L.R q := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  refine ⟨⟨fun r hr => (kt.gpr r fun h => hr (by simp at h; simp [h, fnClob])).trans (k₂.gpr r hr),
      kt.rd.trans k₂.rd, kt.wr.trans k₂.wr, kt.sp.trans k₂.sp⟩, ?_, ?_, ?_⟩
  · refine ((keep_unch k₂ fun w hw => ?_).trans ot).cover fun w hw => ?_
    · simp only [ladWs, List.mem_append]; exact .inl (.inr hw)
    · rcases List.mem_append.mp hw with hw | hw
      · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        all_goals exact ⟨_, mem_ladWx (by mem_list), Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [ex, ey, ez]
    exact ⟨I₂.lt _ (dW _ (by simp)), I₂.lt _ (dW _ (by simp)), I₂.lt _ (dW _ (by simp))⟩
  · show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [ex, ey, ez, I₂.val _ (dW _ (by simp)), I₂.val _ (dW _ (by simp)), I₂.val _ (dW _ (by simp))]
    exact t₂

/-! ## An iteration, and the comb -/

/-- An iteration: digit `j - 1` added to the accumulator. -/
theorem stepI_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true)
    {s : State} {base T : Addr} {k j : Nat}
    (i : InputsI K C tbl base T k s) (acc : Acc K C base k j s)
    (hj : 1 ≤ j) (hJ : j ≤ K.J) (hk : k < 2 ^ K.L.nbits) (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    WP isa K.stepI s fun t =>
      Rk powClob s t ∧ Unch base (ladWx K.L) s.mem t.mem ∧
      InputsI K C tbl base T k t ∧ Acc K C base k (j - 1) t ∧ t.gpr .r31 = BitVec.ofNat 64 (j - 1) := by
  apply WP.of_syms
  unfold TCombCfg.stepI
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  refine WP.seq (wp_decCounter hj gj (WP.block_nil ?_))
  generalize hu : s.write .r31 (BitVec.ofNat 64 (j - 1)) = u
  have ku : Kp [.r31] s u := by rw [← hu]; exact Kp.write _ _ (by decide)
  have gu : u.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hu]; simp only [write_gpr, ite_true]
  have mu : u.mem = s.mem := by rw [← hu]; rfl
  have syu : u.syms = s.syms := by rw [← hu]; rfl
  have iu : InputsI K C tbl base T k u :=
    i.keep h.layout hd (ku.rk (rs' := [.r31])) (by decide) (by rw [mu]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (entryI_ok K h hC iu (by omega) hk gu hd) fun v ⟨kv, ov, rv, lv, pv⟩ syv => ?_)
  have iv : InputsI K C tbl base T k v := iu.keep h.layout hd kv (by decide) ov syv
  have rlt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal v.mem base x K.L.M.n < C.p := by
    intro x hx
    rw [rv x hx, mu]
    exact acc.lt x hx
  have rrep : Rep C (tmv C K.L.M.n base v K.L.R.x) (tmv C K.L.M.n base v K.L.R.y)
      (tmv C K.L.M.n base v K.L.R.z) (mul (combEW K.w k K.J j) (G C)) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [rv _ (by simp), rv _ (by simp), rv _ (by simp), mu]
    exact acc.rep
  have hlt : ∀ x ∈ rcbR K.L.S K.L.R K.Q, wordsVal v.mem base x K.L.M.n < C.p := by
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨iv.coeffA ▸ Nat.mod_lt _ hp, iv.coeffB ▸ Nat.mod_lt _ hp, rlt _ (by simp), rlt _ (by simp),
      rlt _ (by simp), lv _ (by simp), lv _ (by simp), lv _ (by simp)⟩
  have hq : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], x ∈ ladSlots K.L := by
    rw [h.layout.qT]
    intro x hx
    exact ladPts_slots K.L x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])
  unfold TCombCfg.addI
  refine WP.mono_syms (addI_gen h.layout.lad (h.layout.qT ▸ h.layout.apart) hq
    (by rw [h.fieldK, h.fieldM]; exact h.modulus) h.fieldK h.fieldM h.unit iv.wsr hlt)
    fun t ⟨kt, ot, lt, et⟩ syt => fun syt' => ?_
  have keep : Rk powClob s t :=
    (ku.rk (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))
  have unch : Unch base (ladWx K.L) s.mem t.mem := by
    have ou : Unch base (ladWx K.L) s.mem u.mem := by rw [mu]; exact Unch.refl _ _ _
    exact (ou.trans (ov.trans ot)).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨keep, unch, i.keep h.layout hd keep (by decide) unch syt', ⟨lt, ?_⟩,
    by rw [kt.g, kv.g]; exact gu⟩
  have pa : Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y)
      (tmv C K.L.M.n base t K.L.R.z)
      (Spec.Weierstrass.add (mul (combEW K.w k K.J j) (G C)) (signedPtW C K.w k (j - 1))) := by
    apply hC.add (hC.onCurve_mul hG _) (by
      unfold signedPtW combPtW
      split
      · exact hC.onCurve_mul hG _
      · exact onCurve_negPt (hC.onCurve_mul hG _)) rrep pv
    rw [et]
    show rcbAddC C _ _ _ _ _ _ = VG.Proof.Weierstrass.rcbAdd (toM _ _ _) (toM _ _ _) _ _ _ _ _ _
    rw [iv.coeffA, iv.coeffB, toM_mont h.unit, toM_mont h.unit]
  have eqj : j - 1 + 1 = j := by omega
  have sum := combW_add hC hG (w := K.w) (k := k) (j := j - 1) (J := K.J) (by omega)
  change Spec.Weierstrass.add _ (signedPtW C K.w k (j - 1)) = _ at sum
  rw [eqj] at sum
  rw [sum] at pa
  exact pa

/-- `R = S`, and `r31 = J`. -/
theorem startI_ok (K : TCombCfg) {s : State} {base : Addr} (h : LayoutI K) (hw : WsReg s base)
    (hx : K.start.1 < 2 ^ (64 * K.L.M.n)) (hy : K.start.2 < 2 ^ (64 * K.L.M.n))
    (hz : K.one < 2 ^ (64 * K.L.M.n)) (hJ : K.J < 2 ^ 15) :
    WP isa (.block (Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.x K.start.1 ++
      Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.y K.start.2 ++
      Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.z K.one ++ ([.li .r31 K.J] : List Instr))) s fun t =>
      Kp [.r11, .r31] s t ∧ Unch base (ladWx K.L) s.mem t.mem ∧
      t.gpr .r31 = BitVec.ofNat 64 K.J ∧
      wordsVal t.mem base K.L.R.x K.L.M.n = K.start.1 ∧ wordsVal t.mem base K.L.R.y K.L.M.n = K.start.2 ∧
      wordsVal t.mem base K.L.R.z K.L.M.n = K.one := by
  obtain ⟨hown, lo, -⟩ := h.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo
  obtain ⟨⟨rx, -⟩, ⟨ry, -⟩, ⟨rz, -⟩, -⟩ := lo
  have rne : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], ∀ y ∈ [K.L.R.x, K.L.R.y, K.L.R.z], x ≠ y →
      x + 8 * K.L.M.n ≤ y ∨ y + 8 * K.L.M.n ≤ x := fun x hx y hy hne =>
    h.lad.lay.lay.apart x y (ladPts_slots K.L x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h]))
      (ladPts_slots K.L y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; rcases hy with h | h | h <;> simp [h])) hne
  obtain ⟨rxy, rxz, ryz⟩ := h.lad.lay.rne
  have axy := rne _ (by simp) _ (by simp) rxy
  have axz := rne _ (by simp) _ (by simp) rxz
  have ayz := rne _ (by simp) _ (by simp) ryz
  have nowrap := hw.nowrap
  rw [List.append_assoc, List.append_assoc]
  refine wp_append (WP.mono (setConstW_ok hw (o := K.L.R.x) (by omega) hx) fun v ⟨ov, xv, kv⟩ => ?_)
  have wv := hw.of_kp kv
  refine wp_append (WP.mono (setConstW_ok wv (o := K.L.R.y) (by omega) hy) fun a ⟨oa, ya, ka⟩ => ?_)
  have wa := wv.of_kp ka
  refine wp_append (WP.mono (setConstW_ok wa (o := K.L.R.z) (by omega) hz) fun b ⟨ob, zb, kb⟩ => ?_)
  refine wp_step (exec_li hJ) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, ite_true]
  have ub : Unch base [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n)] s.mem b.mem :=
    ov.unch.trans (oa.unch.trans ob.unch)
  refine ⟨((kv.mono (by decide)).trans ((ka.mono (by decide)).trans (kb.mono (by decide)))).trans
      (Kp.write _ _ (by decide)), ?_, trivial, ?_, ?_, zb⟩
  · refine ub.cover fun w hw' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    all_goals exact ⟨_, mem_ladWx (by mem_list), Nat.le_refl _, Nat.le_refl _⟩
  · rw [ob.wordsVal (by omega) (by omega), oa.wordsVal (by omega) (by omega), xv]
  · rw [ob.wordsVal (by omega) (by omega), ya]

/-- The comb: `R = [k]G`, for the scalar `k` of `nbits` bits whose table of
bits is at `bits`, reduced, with only the registers of `powClob` and the
ladder's writes changed. -/
theorem combI_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true)
    {s : State} {base T : Addr} {k : Nat} (hw : WsReg s base)
    (ht : TableMem s T (tableWords K C tbl)) (sym : s.syms K.tsym = T)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩)
    (hk : k < 2 ^ K.L.nbits) (zero : wordsVal s.mem base K.zero K.L.M.n = 0)
    (bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0)
    (coeffA : wordsVal s.mem base K.L.S.a K.L.M.n = C.a * 2 ^ (64 * K.L.M.n) % C.p)
    (coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n = (3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p) :
    WP isa K.combI s fun t =>
      Rk powClob s t ∧ Unch base (ladWx K.L) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y) (tmv C K.L.M.n base t K.L.R.z)
        (mul k (G C)) := by
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have fit := h.modulus.m_lt
  have sx : K.start.1 < C.p := by rw [h.startX]; exact Nat.mod_lt _ hp
  have sy : K.start.2 < C.p := by rw [h.startY]; exact Nat.mod_lt _ hp
  unfold TCombCfg.combI
  refine WP.seq (WP.mono_syms (startI_ok K h.layout hw (Nat.lt_trans sx fit) (Nat.lt_trans sy fit)
    (Nat.lt_trans h.one_lt fit) h.J15) fun u ⟨ku, ou, gu, xu, yu, zu⟩ syu => ?_)
  have i₀ : InputsI K C tbl base T k s := ⟨hw, ht, sym, zero, bits, coeffA, coeffB⟩
  have iu : InputsI K C tbl base T k u := i₀.keep h.layout hd (ku.rk (rs' := [.r11, .r31])) (by decide) ou syu
  have au : Acc K C base k K.J u := by
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [xu, yu, zu]
      exact ⟨sx, sy, h.one_lt⟩
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [xu, yu, zu, h.startX, h.startY, toM_mont h.unit, toM_mont h.unit, h.one, combEW_top, h.tables.start]
      exact rep_affine' hC _ _
  let Inv := fun j t => InputsI K C tbl base T k t ∧ Acc K C base k j t ∧
    t.gpr .r31 = BitVec.ofNat 64 j ∧ Rk powClob s t ∧ Unch base (ladWx K.L) s.mem t.mem
  refine countLoop_ok (Inv := Inv) (fun j t hi => hi.2.2.1) (fun j t hj hJ hi => ?_) (fun t hi => ?_) h.J1
    (by have := h.J15; omega) ⟨iu, au, gu, ku.rk (by decide), ou⟩
  · obtain ⟨it, accT, gt, kt, ot⟩ := hi
    refine WP.mono (stepI_ok K h hC hG it accT hj hJ hk gt hd) fun v ⟨kv, ov, iv, av, gv⟩ => ?_
    refine ⟨iv, av, gv, kt.trans kv, ?_⟩
    exact (ot.trans ov).cover fun w hw' => ⟨w, by
      simpa only [List.mem_append, or_self] using hw', Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨_, accT, _, kt, ot⟩ := hi
    refine ⟨kt, ot, accT.lt, ?_⟩
    have hk' : k < 2 ^ (K.w * K.J) := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) h.coverBits)
    simpa only [combEW_zero hk'] using accT.rep

end VG.Proof.Weierstrass.PPC64LE.TComb
