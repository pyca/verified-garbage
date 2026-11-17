module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombI
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.CombDigitTopW
import VerifiedGarbage.Proof.Weierstrass.CombPointW
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# The comb's `[k]G` with the addition inlined, on 32-bit ARM

`combI` (`Impl/Weierstrass/Arm/TCombI.lean`), for coordinates of more than
6 words, on the ladder's layout (`LayoutI`): the comb's window, digit, scan
and sign (`Proof/Weierstrass/Arm/TCombCorrect.lean`), the entry selected to
the ladder's `T`, and `R = R + T` by the complete addition inlined into `D`
(`rcb_ok`), then copied to `R`. `combI_ok`: `R = [k]G`, reduced, with only
the registers of `powClob` and the ladder's writes (`ladWx`) changed.
-/

-- separate module: the comb of the curves of more than 6 words, which each one's configuration imports

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.TComb

open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Point VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Point
open VG.Impl.Weierstrass.Arm.Mont (own)
open Spec.Weierstrass

/-! ## The layout -/

/-- The ladder's layout, the entry selected to its `T`, `-y` in `D`'s `x`,
zero in a slot the ladder does not write, and the addition's slots apart. -/
structure LayoutI (K : TCombCfg) : Prop where
  lad : LadLay K.L 4096 8192
  wk : LadWk K.L 4096 (own K.L.M.n)
  qT : K.Q = K.L.T
  negD : K.neg = K.L.D.x
  zeroLe : K.zero + 8 * K.L.M.n ≤ own K.L.M.n
  zeroW : ∀ w ∈ ladWx K.L (own K.L.M.n), K.zero + 8 * K.L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.zero
  apart : RcbApart K.L.S K.L.R K.L.T K.L.D

theorem mem_ladWx {L : LadderCfg} {wk x : Nat} (h : x ∈ ladWs L) : (x, 8 * L.M.n) ∈ ladWx L wk := by
  simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton]
  exact .inl (.inl ⟨x, h, rfl⟩)

theorem own_ladWx (L : LadderCfg) (wk : Nat) : (wk, 64 * L.M.n) ∈ ladWx L wk := by
  simp [ladWx]

/-- The numbers of the slots the entry uses. -/
theorem LayoutI.nums {K : TCombCfg} (h : LayoutI K) :
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.Q.x, K.Q.y, K.Q.z, K.neg, K.zero, K.L.S.a, K.L.S.b3],
      x + 8 * K.L.M.n ≤ own K.L.M.n) ∧
    K.Q.y = K.Q.x + 8 * K.L.M.n ∧ K.Q.z = K.Q.x + 16 * K.L.M.n ∧
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.zero, K.neg], x + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ x) ∧
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.zero], K.neg + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.neg) ∧
    (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], K.zero + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.zero) := by
  have hL := h.lad
  obtain sl : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.L.T.x, K.L.T.y, K.L.T.z, K.L.D.x, K.L.S.a,
      K.L.S.b3], x ∈ ladSlots K.L := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (refine ladPts_slots K.L _ ?_; simp; done)
      | (refine ladR_slots K.L _ ?_; simp [ladR, ladRo]; done)
  obtain ap : ∀ {x y}, x ∈ ladSlots K.L → y ∈ ladSlots K.L → x ≠ y →
      x + 8 * K.L.M.n ≤ y ∨ y + 8 * K.L.M.n ≤ x := fun hx hy hne => hL.lay.apart _ _ hx hy hne
  obtain le : ∀ {x}, x ∈ ladSlots K.L → x + 8 * K.L.M.n ≤ own K.L.M.n := fun hx => h.wk.sl _ hx
  obtain qx : K.Q.x = K.L.T.x := by rw [h.qT]
  obtain qy : K.Q.y = K.L.T.y := by rw [h.qT]
  obtain qz : K.Q.z = K.L.T.z := by rw [h.qT]
  obtain hqy : K.Q.y = K.Q.x + 8 * K.L.M.n := rfl
  obtain hqz : K.Q.z = K.Q.x + 16 * K.L.M.n := by
    simp only [TCombCfg.Q, ptAt, Impl.Weierstrass.Point.elemBytes]
    omega_using []
  have nd := h.negD
  -- what differs from what
  obtain rT : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], ∀ y ∈ [K.L.T.x, K.L.T.y, K.L.T.z, K.L.D.x], x ≠ y :=
    fun x hx y hy e => hL.rdt x hx (by
      subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with h | h | h | h <;> simp [h])
  obtain zA : ∀ y ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.L.T.x, K.L.T.y, K.L.T.z, K.L.D.x],
      K.zero + 8 * K.L.M.n ≤ y ∨ y + 8 * K.L.M.n ≤ K.zero :=
    fun y hy => h.zeroW _ (mem_ladWx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with h | h | h | h | h | h | h <;> rw [h] <;> mem_list))
  obtain tD : ∀ y ∈ [K.L.T.x, K.L.T.y, K.L.T.z], y ≠ K.L.D.x := fun y hy e =>
    h.apart.apart y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with h | h | h <;> rw [h] <;> mem_list) (by rw [e]; mem_list)
  refine ⟨?_, hqy, hqz, ?_, ?_, ?_⟩
  · intro x hx
    rw [qx, qy, qz, nd] at hx
    by_cases hz : x = K.zero
    · subst hz; exact h.zeroLe
    exact le (sl x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h | h | h
      all_goals first | exact absurd h hz | simp only [h, true_or, or_true]))
  · have tx := sl K.L.T.x (by simp)
    obtain ty := sl K.L.T.y (by simp)
    obtain tz := sl K.L.T.z (by simp)
    obtain hty : K.L.T.y = K.L.T.x + 8 * K.L.M.n := by rw [← qy, ← qx]; exact hqy
    obtain htz : K.L.T.z = K.L.T.x + 16 * K.L.M.n := by rw [← qz, ← qx]; exact hqz
    obtain apT : ∀ {x}, x ∈ ladSlots K.L → x ≠ K.L.T.x → x ≠ K.L.T.y → x ≠ K.L.T.z →
        x + 8 * K.L.M.n ≤ K.L.T.x ∨ K.L.T.x + 24 * K.L.M.n ≤ x := fun hx a b c => by
      have := ap hx tx a; have := ap hx ty b; have := ap hx tz c; omega_arith
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
    · have := zA K.L.T.x (by simp); have := zA K.L.T.y (by simp); have := zA K.L.T.z (by simp); omega_arith
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

/-- What the ladder writes is in the first 4096 bytes of the working space. -/
theorem LayoutI.bounded {K : TCombCfg} (h : LayoutI K) :
    ∀ w ∈ ladWx K.L (own K.L.M.n), 0 ≤ w.1 ∧ w.1 + w.2 ≤ 4096 := by
  intro w hw
  have := h.wk.le
  have := h.wk.tmp
  simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with (⟨y, hy, rfl⟩ | rfl) | rfl
  · exact ⟨Nat.zero_le _, h.lad.lay.le y (ladWs_slots K.L y hy)⟩
  · exact ⟨Nat.zero_le _, by dsimp only; omega_arith⟩
  · exact ⟨Nat.zero_le _, by dsimp only; omega_arith⟩

/-! ## What every iteration keeps -/

/-- What every iteration keeps: the working space, the modulus, the table,
zero, the scalar's bits, and the ladder's `a` and `3b` (in Montgomery's
form). -/
structure InputsI (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (base T : Addr) (k : Nat)
    (s : State) : Prop where
  scr : Scr s base 4096
  far : Far s base 8192
  mod : ModOkW K.L.M 4096 C.p s.mem base
  table : TableMem s T (tableWords K C tbl)
  symbol : State.addr (s.syms K.tsym) = T
  zero : wordsVal s.mem base K.zero K.L.M.n = 0
  bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0
  coeffA : wordsVal s.mem base K.L.S.a K.L.M.n = C.a * 2 ^ (64 * K.L.M.n) % C.p
  coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n = (3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p

theorem InputsI.keep {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))} {base T : Addr} {k : Nat}
    {s t : State} {rs : List Reg} (i : InputsI K C tbl base T k s) (h : LayoutI K)
    (hb : 4096 ≤ K.L.bits) (hend : K.L.bits + K.L.nbits ≤ 8192)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 4096⟩)
    (keep : Rest rs s t) (r12 : Reg.r12 ∉ rs) (mem : Unch base (ladWx K.L (own K.L.M.n)) s.mem t.mem)
    (syms : t.syms = s.syms) : InputsI K C tbl base T k t := by
  obtain ⟨lo, -⟩ := h.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo
  obtain ⟨-, -, -, -, -, -, -, z, a, b⟩ := lo
  have hown := h.wk.le
  have nowrap := i.scr.nowrap
  have bounded := h.bounded
  obtain frame : Frame [⟨base, 4096⟩] s.mem t.mem := outside_frame
    (mem.outside (o := 0) (n := 4096) bounded) (Nat.le_refl _)
  obtain ro : ∀ x ∈ [K.L.S.a, K.L.S.b3], ∀ w ∈ ladWx K.L (own K.L.M.n), x + 8 * K.L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ladLay_apart_wx h.lad h.wk (ladR_slots K.L _ (by simp [ladR, ladRo])) (h.lad.ro _ (by simp [ladRo]))
    · exact ladLay_apart_wx h.lad h.wk (ladR_slots K.L _ (by simp [ladR, ladRo])) (h.lad.ro _ (by simp [ladRo]))
  obtain hmo : ∀ w ∈ ladWx K.L (own K.L.M.n), K.L.M.mo + 8 * K.L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.L.M.mo := by
    intro w hw
    simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with (⟨y, hy, rfl⟩ | rfl) | rfl
    · exact (h.lad.lay.mo y (ladWs_slots K.L y hy)).symm
    · exact i.mod.sep
    · exact .inl h.wk.mo
  have hM := i.mod
  have hmo4 := hM.mo
  refine ⟨i.scr.of_rest keep r12, i.far.of_rest keep,
    ⟨hM.n0, hM.mo, hM.tmp, hM.sep, by rw [mem.wordsVal hmo (by omega_using [hmo4, nowrap])]; exact hM.val,
      hM.inv, hM.red⟩,
    i.table.of_frame (by rw [keep.rd, keep.wr]) frame (by simpa only [List.mem_singleton, forall_eq] using hd),
    by rw [syms]; exact i.symbol, ?_, ?_, ?_, ?_⟩
  · rw [mem.wordsVal h.zeroW (by omega_using [z, hown]), i.zero]
  · intro j hj
    rw [mem.byte (fun w hw => .inr (by have := bounded w hw; omega_using [hb, this])) (by omega_using [hend, hj]),
      i.bits j hj]
  · rw [mem.wordsVal (ro _ (by simp)) (by omega_using [a, hown]), i.coeffA]
  · rw [mem.wordsVal (ro _ (by simp)) (by omega_using [b, hown]), i.coeffB]

/-! ## The signed entry -/

/-- `y = -y` if the digit is negative: `-y` into `D`'s `x` by the field's
subtraction from zero, then the selection by the sign's mask. -/
theorem negateI_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} (positive : Prop) [Decidable positive]
    (h : LayoutI K) (hs : Scr s base 4096) (hf : Far s base 8192)
    (hm : K.F.m = m) (hn : K.F.k = K.L.M.n) (hM : VG.Proof.Weierstrass.Arm.Mont.ModOk K.L.M.n m)
    (hz : wordsVal s.mem base K.zero K.L.M.n = 0) (hy : wordsVal s.mem base K.Q.y K.L.M.n < m)
    (hmask : ∀ u, Rest VG.Proof.Weierstrass.Arm.Mont.callClob s u →
      Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem u.mem →
      WP isa K.signMask u fun v =>
        v.gpr .r10 = (if positive then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4, .r10] u v) :
    WP isa (.seq (VG.Impl.Weierstrass.Arm.Mont.subCall K.F K.neg K.zero K.Q.y)
      (.seq K.signMask (.block (sel (2 * K.L.M.n) K.Q.y K.Q.y K.neg)))) s fun t =>
      Rest VG.Proof.Weierstrass.Arm.Mont.callClob s t ∧
      Unch base ([(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] ++ [(K.Q.y, 8 * K.L.M.n)]) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      wordsVal t.mem base K.Q.x K.L.M.n = wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n =
        (if positive then wordsVal s.mem base K.Q.y K.L.M.n else (m - wordsVal s.mem base K.Q.y K.L.M.n) % m) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = wordsVal s.mem base K.Q.z K.L.M.n := by
  obtain ⟨lo, hqy, hqz, qap, nap, -⟩ := h.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo qap nap
  obtain ⟨rx, ry, rz, qx, qy, qz, ng, zr, -, -⟩ := lo
  obtain ⟨qrx, qry, qrz, -, qng⟩ := qap
  obtain ⟨nrx, nry, nrz, -⟩ := nap
  have hown := h.wk.le
  have nowrap := hs.nowrap
  obtain fm : VG.Proof.Weierstrass.Arm.Mont.ModOk K.F.k K.F.m := by rw [hn, hm]; exact hM
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.Arm.Mont.subCall_ok fm hs hf
    (by rw [hn]; exact ng) (by rw [hn]; exact zr) (by rw [hn]; exact qy)
    (by rw [hn, hm, hz]; omega_using [hy]) (by rw [hn, hm]; exact hy)) fun u ⟨ku, yu⟩ => ?_)
  rw [hn, hm, hz, Nat.zero_add] at yu
  obtain ou := Outs.unch ku.mem
  rw [hn] at ou
  refine WP.seq (WP.mono (hmask u ku.rest ou) fun v ⟨mask, kv⟩ => ?_)
  obtain hsv := (hs.of_rest ku.rest (by decide)).of_rest kv.keep (by decide)
  obtain msk : v.gpr .r10 = if decide (¬positive) then BitVec.allOnes 32 else 0 := by
    rw [mask]
    by_cases hp : positive <;> simp [hp]
  refine WP.mono (selField_ok hsv (decide (¬positive)) msk
    (o := K.Q.y) (a := K.Q.y) (b := K.neg) (n := K.L.M.n)
    (by omega_using [qy, hown]) (by omega_using [qy, hown]) (by omega_using [ng, hown])
    (.inl (Nat.le_refl _)) (by omega_using [hqy, qng])) fun t ⟨yt, kt, ot⟩ => ?_
  obtain qold : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    rw [kv.mem]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply ou.wordsVal _ (by rcases hx with rfl | rfl | rfl <;> omega_using [qx, qy, qz, hown])
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rcases hx with rfl | rfl | rfl
    · exact ⟨by omega_using [qng], .inl qx⟩
    · exact ⟨by omega_using [hqy, qng], .inl qy⟩
    · exact ⟨by omega_using [hqz, qng], .inl qz⟩
  refine ⟨ku.rest.trans ((kv.keep.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob, VG.Proof.Mont.Arm.clob])).trans
    (kt.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob, VG.Proof.Mont.Arm.clob]))), ?_, ?_, ?_, ?_, ?_⟩
  · have ov : Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem v.mem := by
      rw [kv.mem]; exact ou
    exact ov.trans ot.unch
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain lowx : x + 8 * K.L.M.n ≤ own K.L.M.n := by rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    obtain negx : K.neg + 8 * K.L.M.n ≤ x ∨ x + 8 * K.L.M.n ≤ K.neg := by
      rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    obtain qx' : x + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ x := by
      rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    rw [ot.wordsVal (by omega_using [hqy, qx']) (by omega_using [lowx, hown]), kv.mem]
    apply ou.wordsVal _ (by omega_using [lowx, hown])
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨negx.symm, .inl lowx⟩
  · rw [ot.wordsVal (by omega_using [hqy]) (by omega_using [qx, hown]), qold _ (by simp)]
  · rw [yt, kv.mem, yu]
    obtain qo := qold K.Q.y (by simp)
    rw [kv.mem] at qo
    rw [qo]
    by_cases hp : positive <;> simp [hp]
  · rw [ot.wordsVal (by omega_using [hqy, hqz]) (by omega_using [qz, hown]), qold _ (by simp)]

/-- The side conditions of a comb with the addition inlined, which do not
depend on the scalar. -/
structure ConfigI (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (start : Nat × Nat) : Prop where
  layout : LayoutI K
  fieldK : K.F.k = K.L.M.n
  fieldM : K.F.m = C.p
  modulus : VG.Proof.Weierstrass.Arm.Mont.ModOk K.L.M.n C.p
  unit : UnitMod C.p (2 ^ (64 * K.L.M.n))
  tables : CombOkW C K.w K.J tbl start
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.L.M.n)) K.one = 1
  startX : K.start.1 = start.1 * 2 ^ (64 * K.L.M.n) % C.p
  startY : K.start.2 = start.2 * 2 ^ (64 * K.L.M.n) % C.p
  w1 : 1 ≤ K.w
  w9 : K.w < 9
  J1 : 1 ≤ K.J
  J32 : K.J < 2 ^ 32
  startBits : K.w * (K.J - 1) ≤ K.L.nbits
  coverBits : K.L.nbits ≤ K.w * K.J
  bitsLow : 4096 ≤ K.L.bits
  bitsHigh : K.L.bits + K.L.nbits ≤ 8192
  bitsFit : K.L.bits < 8192
  windowFit : K.L.bits % 4096 + K.w ≤ 4096
  encJ : encodable (BitVec.ofNat 32 K.J) = true
  encLast : encodable (BitVec.ofNat 32 (K.J - 1)) = true
  encRow : encodable (BitVec.ofNat 32 (16 * K.L.M.n * K.H)) = true
  encEntry : encodable (BitVec.ofNat 32 (16 * K.L.M.n)) = true
  encH : encodable (BitVec.ofNat 32 (K.H + 1)) = true

theorem ConfigI.magnitude {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) (k j : Nat) : magH K.H (combWin K.w k j) ≤ K.H := by
  apply magH_le
  obtain pow : 2 ^ K.w = 2 * K.H := by
    change 2 ^ K.w = 2 * 2 ^ (K.w - 1)
    calc
      2 ^ K.w = 2 ^ ((K.w - 1) + 1) := congrArg (fun n => 2 ^ n) (by have := h.w1; omega_using [this])
      _ = 2 * 2 ^ (K.w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [← pow]
  exact combWin_lt _ _ _

theorem ConfigI.halfBound {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) : K.H + 1 < 2 ^ 31 := by
  have hw := h.w9
  obtain bound : K.H ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  omega_using [bound]

theorem unch_three {base : Addr} {o n : Nat} {m m' : Mem} (h : Unch base [(o, 24 * n)] m m') :
    Unch base [(o, 8 * n), (o + 8 * n, 8 * n), (o + 16 * n, 8 * n)] m m' := fun x hx => h x (by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx ⊢
  omega_using [hx])

/-- What the entry writes is the ladder's. -/
theorem LayoutI.entry_cover {K : TCombCfg} (h : LayoutI K) :
    ∀ w ∈ [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] ++ [(K.Q.y, 8 * K.L.M.n)] ++
      [(K.Q.x, 8 * K.L.M.n), (K.Q.x + 8 * K.L.M.n, 8 * K.L.M.n), (K.Q.x + 16 * K.L.M.n, 8 * K.L.M.n)],
      ∃ v ∈ ladWx K.L (own K.L.M.n), v.1 ≤ w.1 ∧ w.1 + w.2 ≤ v.1 + v.2 := by
  obtain ⟨-, hqy, hqz, -⟩ := h.nums
  obtain qx : K.Q.x = K.L.T.x := by rw [h.qT]
  obtain qy : K.Q.y = K.L.T.y := by rw [h.qT]
  obtain qz : K.Q.z = K.L.T.z := by rw [h.qT]
  obtain mem : ∀ x ∈ [K.L.D.x, K.L.T.x, K.L.T.y, K.L.T.z], (x, 8 * K.L.M.n) ∈ ladWx K.L (own K.L.M.n) := by
    intro x hx
    apply mem_ladWx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> mem_list
  intro w hw
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, mem K.L.D.x (by simp), by rw [h.negD], by rw [h.negD]⟩
  · exact ⟨_, own_ladWx K.L _, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, mem K.L.T.y (by simp), by rw [qy], by rw [qy]⟩
  · exact ⟨_, mem K.L.T.x (by simp), by rw [qx], by rw [qx]⟩
  · exact ⟨_, mem K.L.T.y (by simp), by rw [← hqy, qy], by rw [← hqy, qy]⟩
  · exact ⟨_, mem K.L.T.z (by simp), by rw [← hqz, qz], by rw [← hqz, qz]⟩

/-- The entry of digit `j`, signed, in the ladder's `T`. -/
theorem entryI_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) (hC : Law C) {s : State} {base T : Addr} {k j : Nat}
    (i : InputsI K C tbl base T k s) (hj : j < K.J) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 4096⟩) :
    WP isa K.entry s fun t =>
      Rest VG.Proof.Weierstrass.Arm.Mont.callClob s t ∧ Unch base (ladWx K.L (own K.L.M.n)) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      (∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.Q.x) (tmv C K.L.M.n base t K.Q.y) (tmv C K.L.M.n base t K.Q.z)
        (signedPtW C K.w k j) := by
  unfold TCombCfg.entry
  obtain hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  obtain hfit : C.p ≤ 2 ^ (64 * K.L.M.n) := Nat.le_of_lt h.modulus.m_lt
  obtain ⟨lo, hqy, hqz, qap, -, -⟩ := h.layout.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo qap
  obtain ⟨rx, ry, rz, qx, qy, qz, ng, zr, -, -⟩ := lo
  obtain ⟨qrx, qry, qrz, qzr, -⟩ := qap
  have hown := h.layout.wk.le
  have nowrap := i.scr.nowrap
  refine WP.seq (WP.mono_syms (digit_ok K i.scr i.far h.w9 hj (by have := h.J32; omega_using [this])
    h.encLast h.startBits h.coverBits h.bitsFit h.windowFit h.bitsHigh hk gj i.bits)
    fun u ⟨gu, ku⟩ syu => ?_)
  obtain iu : InputsI K C tbl base T k u := i.keep h.layout h.bitsLow h.bitsHigh hd ku.keep
    (by decide) (by rw [ku.mem]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (selectTable_ok K iu.scr
    (by omega_using [hqz, qz, hown]) (by omega_using [zr, hown]) qzr
    (Nat.lt_of_lt_of_le h.one_lt hfit) iu.zero
    (by have := h.modulus.n3; omega_using [this]) h.halfBound (h.magnitude k j) gu
    (by rw [ku.keep.gpr .r11 (by decide), gj]) iu.table iu.symbol h.tables.len h.tables.lenH hj hp hfit hd
    h.encRow h.encEntry h.encH) fun v ⟨xv, yv, zv, kv, ov⟩ syv => ?_)
  obtain ouv : Unch base (ladWx K.L (own K.L.M.n)) u.mem v.mem :=
    (unch_three ov.unch).cover fun w hw => h.layout.entry_cover w (List.mem_append_right _ hw)
  obtain iv : InputsI K C tbl base T k v := iu.keep h.layout h.bitsLow h.bitsHigh hd kv (by decide) ouv syv
  obtain ylt : wordsVal v.mem base K.Q.y K.L.M.n < C.p := by
    rw [yv]; split <;> first | exact h.one_lt | exact Nat.mod_lt _ hp
  obtain oldR : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain lowx : x + 8 * K.L.M.n ≤ own K.L.M.n := by rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    obtain qx' : x + 8 * K.L.M.n ≤ K.Q.x ∨ K.Q.x + 24 * K.L.M.n ≤ x := by
      rcases hx with rfl | rfl | rfl <;> with_reducible assumption
    rw [ov.wordsVal qx' (by omega_using [lowx, hown]), ku.mem]
  obtain mask : ∀ a, Rest VG.Proof.Weierstrass.Arm.Mont.callClob v a →
      Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] v.mem a.mem →
      WP isa K.signMask a fun b =>
        b.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 32) ∧ RegOnly [.r4, .r10] a b := by
    intro a keep mem
    apply signMask_ok K (iv.scr.of_rest keep (by decide)) (iv.far.of_rest keep)
      ⟨h.w1, h.w9⟩ hj (by have := h.J32; omega_using [this]) h.encLast h.startBits h.coverBits h.bitsFit
      h.windowFit h.bitsHigh hk
      (by rw [keep.gpr .r11 (by decide), kv.gpr .r11 (by decide), ku.keep.gpr .r11 (by decide), gj])
    intro b hb
    have hlow := h.bitsLow
    rw [mem.byte (fun w hw => .inr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> (dsimp only; omega_using [ng, hown, hlow])))
      (by have := h.bitsHigh; omega_using [hb, this]), iv.bits b hb]
  refine WP.mono (negateI_ok K (K.H ≤ combWin K.w k j) h.layout iv.scr iv.far
    h.fieldM h.fieldK h.modulus iv.zero ylt mask) fun t ⟨kt, ot, rt, xt, yt, zt⟩ => ?_
  obtain ku' : Rest VG.Proof.Weierstrass.Arm.Mont.callClob s u := ku.keep.mono (by
    simp [VG.Proof.Weierstrass.Arm.Mont.callClob, VG.Proof.Mont.Arm.clob])
  obtain kv' : Rest VG.Proof.Weierstrass.Arm.Mont.callClob u v := kv.mono (by
    simp [VG.Proof.Weierstrass.Arm.Mont.callClob, VG.Proof.Mont.Arm.clob])
  refine ⟨ku'.trans (kv'.trans kt), ?_, fun x hx => (rt x hx).trans (oldR x hx), ?_, ?_⟩
  · have ou : Unch base (ladWx K.L (own K.L.M.n)) s.mem u.mem := by rw [ku.mem]; exact Unch.refl _ _ _
    exact (ou.trans (ouv.trans (ot.cover fun w hw => h.layout.entry_cover w
      (List.mem_append_left _ hw)))).cover fun w hw => ⟨w, by
        simpa only [List.mem_append, or_self] using hw, Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [xt, yt, zt, xv, zv]
    refine ⟨?_, ?_, ?_⟩
    · split <;> first | exact hp | exact Nat.mod_lt _ hp
    · split <;> first | exact ylt | exact Nat.mod_lt _ hp
    · split <;> first | exact hp | exact h.one_lt
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [xt, yt, zt]
    exact combSigned_rep hC h.tables h.unit h.one hj h.w1 xv yv zv ylt

/-! ## The addition -/

/-- `R = R + q` by the complete addition inlined into `D`, then `R = D`,
for `q` of the ladder's slots apart from what `rcb` writes. -/
theorem addI_gen {L : LadderCfg} {C : Curve} {S : Impl.Weierstrass.Mont.Modulus} {q : Pt} {wk : Nat}
    (hL : LadLay L 4096 8192) (hW : LadWk L 4096 wk) (hF : FnOk L.M wk S C.p)
    (hA : RcbApart L.S L.R q L.D) (hq : ∀ x ∈ [q.x, q.y, q.z], x ∈ ladSlots L)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    {s : State} {base : Addr} (hs : Scr s base 4096) (hf : Far s base 8192)
    (hM : ModOkW L.M 4096 C.p s.mem base)
    (hlt : ∀ x ∈ rcbR L.S L.R q, wordsVal s.mem base x L.M.n < C.p) {u : Bool} :
    WP isa (.seq (fprog S (rcb L.S L.R q L.D) u) (.block (copyPt L.M.n L.R L.D))) s fun t =>
      Rest VG.Proof.Weierstrass.Arm.Mont.callClob s t ∧ Unch base (ladWx L wk) s.mem t.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal t.mem base x L.M.n < C.p) ∧
      (tmv C L.M.n base t L.R.x, tmv C L.M.n base t L.R.y, tmv C L.M.n base t L.R.z) =
        VG.Proof.Weierstrass.rcbAdd (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3)
          (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)
          (tmv C L.M.n base s q.x) (tmv C L.M.n base s q.y) (tmv C L.M.n base s q.z) := by
  obtain hSl : ∀ x ∈ rcbW L.S L.D ++ rcbR L.S L.R q, x ∈ ladSlots L := by
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
  obtain I₀ : Inv L.M base 4096 C.p (· ∈ ladSlots L) (rcbR L.S L.R q) (tmv C L.M.n base s) s :=
    ⟨hs, hM, fun x hx => hSl x (List.mem_append_right _ hx), hlt, fun _ _ => rfl, hf⟩
  refine WP.seq (WP.mono (rcb_ok hL.lay hW.wk hF hp hA hSl I₀ (fun x hx => hx))
    fun s₂ ⟨k₂, I₂, t₂, _⟩ => ?_)
  obtain pts := ladPts_slots L
  obtain hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.apart x y (pts x hx) (pts y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.rne
  obtain rD : ∀ d ∈ [L.R.x, L.R.y, L.R.z], ∀ e ∈ [L.D.x, L.D.y, L.D.z], d + 8 * L.M.n ≤ e ∨ e + 8 * L.M.n ≤ d :=
    fun d hd e he => hap d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with h | h | h <;> simp [h]) e
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢; rcases he with h | h | h <;> simp [h])
      fun h' => hL.rdt d hd (by
        subst h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
        rcases he with h | h | h <;> simp [h])
  refine WP.mono (copyPt_ok I₂.scr (n := L.M.n) (o := L.R) (a := L.D)
    (fun d hd => hL.lay.le d (pts d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      rcases hd with h | h | h | h | h | h <;> simp [h])))
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩ rD)
    fun t ⟨ex, ey, ez, kt, ot⟩ => ?_
  obtain dW : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.D ++ rcbR L.S L.R q := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  refine ⟨k₂.rest.trans (kt.mono (by simp [VG.Proof.Weierstrass.Arm.Mont.callClob, VG.Proof.Mont.Arm.clob])),
    ?_, ?_, ?_⟩
  · refine ((k₂.unch.mono fun w hw => progW_ladWx mem_ladW_D w hw).trans (Outs.unch ot)).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact List.mem_append_left _ (mem_ladW_R w hw)
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
    (hj : 1 ≤ j) (hJ : j ≤ K.J) (hk : k < 2 ^ K.L.nbits) (gj : s.gpr .r11 = BitVec.ofNat 32 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 4096⟩) :
    WP isa K.stepI s fun t =>
      Rest powClob s t ∧ Unch base (ladWx K.L (own K.L.M.n)) s.mem t.mem ∧
      InputsI K C tbl base T k t ∧ Acc K C base k (j - 1) t ∧
      t.gpr .r11 = BitVec.ofNat 32 (j - 1) ∧ t.z = decide (j - 1 = 0) := by
  apply WP.of_syms
  unfold TCombCfg.stepI
  obtain hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  obtain dec : WP isa (.block [decCounter]) s fun u =>
      u.gpr .r11 = BitVec.ofNat 32 (j - 1) ∧ RegOnly [.r11] s u :=
    wp_decCounter hj gj fun u up => WP.block_nil ⟨up.gpr, ⟨up.rest (by simp), up.mem⟩⟩
  refine WP.seq (WP.mono_syms dec fun u ⟨gu, ku⟩ syu => ?_)
  obtain iu : InputsI K C tbl base T k u := i.keep h.layout h.bitsLow h.bitsHigh hd ku.keep
    (by decide) (by rw [ku.mem]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (entryI_ok K h hC iu (by omega_using [hj, hJ]) hk gu hd)
    fun v ⟨kv, ov, rv, lv, pv⟩ syv => ?_)
  obtain iv : InputsI K C tbl base T k v := iu.keep h.layout h.bitsLow h.bitsHigh hd kv (by decide) ov syv
  obtain rlt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal v.mem base x K.L.M.n < C.p := by
    intro x hx
    rw [rv x hx, ku.mem]
    exact acc.lt x hx
  obtain rrep : Rep C (tmv C K.L.M.n base v K.L.R.x) (tmv C K.L.M.n base v K.L.R.y)
      (tmv C K.L.M.n base v K.L.R.z) (mul (combEW K.w k K.J j) (G C)) := by
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [rv _ (by simp), rv _ (by simp), rv _ (by simp), ku.mem]
    exact acc.rep
  obtain hlt : ∀ x ∈ rcbR K.L.S K.L.R K.Q, wordsVal v.mem base x K.L.M.n < C.p := by
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨iv.coeffA ▸ Nat.mod_lt _ hp, iv.coeffB ▸ Nat.mod_lt _ hp, rlt _ (by simp), rlt _ (by simp),
      rlt _ (by simp), lv _ (by simp), lv _ (by simp), lv _ (by simp)⟩
  obtain hq : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], x ∈ ladSlots K.L := by
    rw [h.layout.qT]
    intro x hx
    exact ladPts_slots K.L x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h])
  unfold TCombCfg.addI
  refine WP.seq (WP.mono (addI_gen h.layout.lad h.layout.wk
    ⟨h.fieldK, h.fieldM, by rw [h.fieldK, h.fieldM]; exact h.modulus, rfl⟩
    (h.layout.qT ▸ h.layout.apart) hq h.unit iv.scr iv.far iv.mod hlt) fun a ⟨ka, oa, la, ea⟩ => ?_)
  obtain ga : a.gpr .r11 = BitVec.ofNat 32 (j - 1) := by
    rw [ka.gpr .r11 (by decide), kv.gpr .r11 (by decide), gu]
  refine wp_testCounter (by have := h.J32; omega_using [hJ, this]) ga fun t ft zt => WP.block_nil (fun syt => ?_)
  obtain keep : Rest powClob s t := (ku.keep.mono (by simp [powClob])).trans
    ((kv.mono clob_powClob).trans ((ka.mono clob_powClob).trans (ft.rest _)))
  obtain unch : Unch base (ladWx K.L (own K.L.M.n)) s.mem t.mem := by
    rw [ft.mem]
    obtain ou : Unch base (ladWx K.L (own K.L.M.n)) s.mem u.mem := by rw [ku.mem]; exact Unch.refl _ _ _
    exact (ou.trans (ov.trans oa)).cover fun w hw => ⟨w, by
      simpa only [List.mem_append, or_self] using hw, Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨keep, unch, i.keep h.layout h.bitsLow h.bitsHigh hd keep (by decide) unch syt,
    ⟨by rw [ft.mem]; exact la, ?_⟩, by rw [ft.gpr, ga], zt⟩
  obtain pa : Rep C (tmv C K.L.M.n base a K.L.R.x) (tmv C K.L.M.n base a K.L.R.y)
      (tmv C K.L.M.n base a K.L.R.z)
      (Spec.Weierstrass.add (mul (combEW K.w k K.J j) (G C)) (signedPtW C K.w k (j - 1))) := by
    apply hC.add (hC.onCurve_mul hG _) (by
      unfold signedPtW combPtW
      split
      · exact hC.onCurve_mul hG _
      · exact onCurve_negPt (hC.onCurve_mul hG _)) rrep pv
    rw [ea]
    show rcbAddC C _ _ _ _ _ _ = VG.Proof.Weierstrass.rcbAdd (toM _ _ _) (toM _ _ _) _ _ _ _ _ _
    rw [iv.coeffA, iv.coeffB, toM_mont h.unit, toM_mont h.unit]
  obtain eqj : j - 1 + 1 = j := by omega_using [hj]
  obtain sum := combW_add hC hG (w := K.w) (k := k) (j := j - 1) (J := K.J) (by omega_using [hj, hJ])
  change Spec.Weierstrass.add _ (signedPtW C K.w k (j - 1)) = _ at sum
  rw [eqj] at sum
  rw [sum] at pa
  simpa only [tmv, ft.mem] using pa

/-- `R = S`, and `r11 = J`. -/
theorem startI_ok (K : TCombCfg) {s : State} {base : Addr} (h : LayoutI K) (hs : Scr s base 4096)
    (hx : K.start.1 < 2 ^ (64 * K.L.M.n)) (hy : K.start.2 < 2 ^ (64 * K.L.M.n))
    (hz : K.one < 2 ^ (64 * K.L.M.n)) (encJ : encodable (BitVec.ofNat 32 K.J) = true) :
    WP isa (.block (setConst K.L.M.n K.L.R.x K.start.1 ++ setConst K.L.M.n K.L.R.y K.start.2 ++
      setConst K.L.M.n K.L.R.z K.one ++ ([.mov .r11 (.imm (BitVec.ofNat 32 K.J))] : List Instr))) s fun t =>
      Rest [.r4, .r11] s t ∧ Unch base (ladWx K.L (own K.L.M.n)) s.mem t.mem ∧
      t.gpr .r11 = BitVec.ofNat 32 K.J ∧
      wordsVal t.mem base K.L.R.x K.L.M.n = K.start.1 ∧ wordsVal t.mem base K.L.R.y K.L.M.n = K.start.2 ∧
      wordsVal t.mem base K.L.R.z K.L.M.n = K.one := by
  obtain ⟨lo, -⟩ := h.nums
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo
  obtain ⟨rx, ry, rz, -⟩ := lo
  have hown := h.wk.le
  obtain rne : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], ∀ y ∈ [K.L.R.x, K.L.R.y, K.L.R.z], x ≠ y →
      x + 8 * K.L.M.n ≤ y ∨ y + 8 * K.L.M.n ≤ x := fun x hx y hy hne =>
    h.lad.lay.apart x y (ladPts_slots K.L x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h]))
      (ladPts_slots K.L y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; rcases hy with h | h | h <;> simp [h])) hne
  obtain ⟨rxy, rxz, ryz⟩ := h.lad.rne
  obtain axy := rne _ (by simp) _ (by simp) rxy
  obtain axz := rne _ (by simp) _ (by simp) rxz
  obtain ayz := rne _ (by simp) _ (by simp) ryz
  have nowrap := hs.nowrap
  rw [List.append_assoc, List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs (by omega_using [rx, hown]) hx) fun v ⟨xv, kv, ov⟩ => ?_
  obtain hsv := hs.of_rest kv (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsv (by omega_using [ry, hown]) hy) fun a ⟨ya, ka, oa⟩ => ?_
  obtain hsa := hsv.of_rest ka (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hsa (by omega_using [rz, hown]) hz) fun b ⟨zb, kb, ob⟩ => ?_
  refine wp_mov (op2_imm encJ) fun t ut => WP.block_nil ?_
  obtain ub : Unch base [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n)] s.mem t.mem := by
    rw [ut.mem]
    exact ov.unch.trans (oa.unch.trans ob.unch)
  refine ⟨(kv.mono (by simp)).trans ((ka.mono (by simp)).trans ((kb.mono (by simp)).trans (ut.rest (by simp)))),
    ub.mono fun w hw => List.mem_append_left _ (mem_ladW_R w hw), ut.gpr, ?_, ?_, ?_⟩
  · rw [ut.mem, ob.wordsVal axz (by omega_using [rx, hown]), oa.wordsVal axy (by omega_using [rx, hown]), xv]
  · rw [ut.mem, ob.wordsVal ayz (by omega_using [ry, hown]), ya]
  · rw [ut.mem, zb]

/-- The comb: `R = [k]G`, for the scalar `k` of `nbits` bits whose table of
bits is at `bits`, reduced, with only the registers of `powClob` and the
ladder's writes changed. -/
theorem combI_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : ConfigI K C tbl start) (hC : Law C) (hG : onCurve C (G C) = true)
    {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base 4096) (hf : Far s base 8192) (hM : ModOkW K.L.M 4096 C.p s.mem base)
    (ht : TableMem s T (tableWords K C tbl)) (sym : State.addr (s.syms K.tsym) = T)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 4096⟩)
    (hk : k < 2 ^ K.L.nbits) (zero : wordsVal s.mem base K.zero K.L.M.n = 0)
    (bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0)
    (coeffA : wordsVal s.mem base K.L.S.a K.L.M.n = C.a * 2 ^ (64 * K.L.M.n) % C.p)
    (coeffB : wordsVal s.mem base K.L.S.b3 K.L.M.n = (3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p) :
    WP isa K.combI s fun t =>
      Rest powClob s t ∧ Unch base (ladWx K.L (own K.L.M.n)) s.mem t.mem ∧
      ModOkW K.L.M 4096 C.p t.mem base ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.L.R.x) (tmv C K.L.M.n base t K.L.R.y) (tmv C K.L.M.n base t K.L.R.z)
        (mul k (G C)) := by
  obtain hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have fit := h.modulus.m_lt
  obtain sx : K.start.1 < C.p := by rw [h.startX]; exact Nat.mod_lt _ hp
  obtain sy : K.start.2 < C.p := by rw [h.startY]; exact Nat.mod_lt _ hp
  unfold TCombCfg.combI
  refine WP.seq (WP.mono_syms (startI_ok K h.layout hs (Nat.lt_trans sx fit) (Nat.lt_trans sy fit)
    (Nat.lt_trans h.one_lt fit) h.encJ) fun u ⟨ku, ou, gu, xu, yu, zu⟩ syu => ?_)
  obtain i₀ : InputsI K C tbl base T k s := ⟨hs, hf, hM, ht, sym, zero, bits, coeffA, coeffB⟩
  obtain iu : InputsI K C tbl base T k u := i₀.keep h.layout h.bitsLow h.bitsHigh hd ku (by decide) ou syu
  obtain au : Acc K C base k K.J u := by
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [xu, yu, zu]
      exact ⟨sx, sy, h.one_lt⟩
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [xu, yu, zu, h.startX, h.startY, toM_mont h.unit, toM_mont h.unit, h.one, combEW_top, h.tables.start]
      exact rep_affine' hC _ _
  let LoopInv := fun j t => InputsI K C tbl base T k t ∧ Acc K C base k j t ∧
    t.gpr .r11 = BitVec.ofNat 32 j ∧ Rest powClob s t ∧ Unch base (ladWx K.L (own K.L.M.n)) s.mem t.mem
  apply countLoop_ok (Inv := LoopInv)
    (fun j t hj hJ hi => ?_) (fun t hi => ?_) h.J1
    ⟨iu, au, gu, ku.mono (by simp [powClob, VG.Proof.Mont.Arm.clob]), ou⟩
  · obtain ⟨it, accT, gt, kt, ot⟩ := hi
    refine WP.mono (stepI_ok K h hC hG it accT hj hJ hk gt hd) fun v ⟨kv, ov, iv, av, gv, zv⟩ => ?_
    refine ⟨⟨iv, av, gv, kt.trans kv, ?_⟩, zv⟩
    exact (ot.trans ov).cover fun w hw => ⟨w, by
      simpa only [List.mem_append, or_self] using hw, Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨it, accT, _, kt, ot⟩ := hi
    refine ⟨kt, ot, it.mod, accT.lt, ?_⟩
    obtain hk' : k < 2 ^ (K.w * K.J) := Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) h.coverBits)
    simpa only [combEW_zero hk'] using accT.rep

end VG.Proof.Weierstrass.Arm.TComb
