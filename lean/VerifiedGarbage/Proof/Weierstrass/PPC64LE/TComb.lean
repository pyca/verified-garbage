module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TCombSelect
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn
import VerifiedGarbage.Proof.Weierstrass.CombPointW
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderPCall
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFn
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# The comb's `[k]G`, on PPC64LE

As on 32-bit ARM (`Proof/Weierstrass/Arm/TCombCorrect.lean` and the modules
it imports): the side conditions of a comb (`Config`), what every iteration
keeps (`Inputs`), the signed entry, the addition, an iteration, and
`comb_ok`: `R = [k]G`, reduced, with only the registers of `powClob` and the
memory of `writes` changed.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.TComb

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)
open VG.Impl.Weierstrass.PPC64LE.Mont (own)
open Spec.Weierstrass

/-- The side conditions of a comb, which do not depend on the scalar. -/
structure Config (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (start : Nat × Nat) : Prop where
  layout : Layout K
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
  J15 : K.J ≤ 2 ^ 15
  startBits : K.w * (K.J - 1) ≤ K.L.nbits
  coverBits : K.L.nbits ≤ K.w * K.J
  bitsOff : K.L.bits + K.w < 2 ^ 15
  row : 16 * K.L.M.n * K.H < 2 ^ 15

theorem Config.magnitude {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (k j : Nat) : magH K.H (combWin K.w k j) ≤ K.H := by
  apply magH_le
  have pow : 2 ^ K.w = 2 * K.H := by
    change 2 ^ K.w = 2 * 2 ^ (K.w - 1)
    calc
      2 ^ K.w = 2 ^ ((K.w - 1) + 1) := congrArg (fun n => 2 ^ n) (by have := h.w1; omega)
      _ = 2 * 2 ^ (K.w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [← pow]
  exact combWin_lt _ _ _

/-- The table's words, for curve `C`. -/
def tableWords (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : List (BitVec 64) :=
  tcombWords K.L.M.n (2 ^ (64 * K.L.M.n)) C.p tbl

/-- What every iteration keeps: the working space, the table, zero, the
scalar's bits, and the point functions' `a` and `3b`. -/
structure Inputs (K : TCombCfg) (base T : Addr) (ws : List (BitVec 64)) (k a b : Nat) (s : State) : Prop where
  wsr : WsReg s base
  table : TableMem s T ws
  symbol : s.syms K.tsym = T
  zero : wordsVal s.mem base K.zero K.L.M.n = 0
  bits : ∀ i < K.L.nbits, s.mem (off base (K.L.bits + i)) = if k.testBit i then 1 else 0
  coeffA : wordsVal s.mem base (aAt K.L.M.n) K.L.M.n = a
  coeffB : wordsVal s.mem base (b3At K.L.M.n) K.L.M.n = b

/-- `Inputs` for the curve `C`: `a` and `3b` in Montgomery's form. -/
abbrev CurveInputs (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) (base T : Addr) (k : Nat)
    (s : State) : Prop :=
  Inputs K base T (tableWords K C tbl) k (C.a * 2 ^ (64 * K.L.M.n) % C.p)
    ((3 * C.b) * 2 ^ (64 * K.L.M.n) % C.p) s

theorem Layout.zero_apart {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ loopWrites K, K.zero + 8 * K.L.M.n ≤ r.1 ∨ r.1 + r.2 ≤ K.zero := by
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low K.zero (by simp)
  have neg := h.negApart K.zero (by simp)
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.zeroApart _ (by simp)
  · exact h.zeroApart _ (by simp)
  · exact h.zeroApart _ (by simp)
  · exact neg.symm
  · exact .inl low
  · exact .inl (by dsimp only; omega_arith)

theorem Layout.params_apart {K : TCombCfg} (h : Layout K) :
    ∀ x ∈ [aAt K.L.M.n, b3At K.L.M.n], ∀ r ∈ loopWrites K, x + 8 * K.L.M.n ≤ r.1 ∨ r.1 + r.2 ≤ x := by
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  intro x hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hx with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega_arith)

theorem Inputs.keep {K : TCombCfg} {base T : Addr} {ws : List (BitVec 64)} {k a b : Nat}
    {s t : State} {rs : List Reg} (i : Inputs K base T ws k a b s) (h : Layout K)
    (hd : Region.Disjoint ⟨T, 8 * ws.length⟩ ⟨base, 8192⟩)
    (keep : Rk rs s t) (r3 : Reg.r3 ∉ rs) (mem : Unch base (loopWrites K) s.mem t.mem)
    (syms : t.syms = s.syms) : Inputs K base T ws k a b t := by
  have := lay_nums h.point.k3 h.point.k6
  have bounded := h.loop_bounded
  have nowrap := i.wsr.nowrap
  have hb := h.point.bits
  have hbe := h.point.bitsE
  have params : ∀ x ∈ [aAt K.L.M.n, b3At K.L.M.n],
      wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    apply mem.wordsVal (h.params_apart x hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega_arith
  refine ⟨i.wsr.of_rk keep r3, i.table.unch (by rw [keep.rd, keep.wr]) mem bounded' hd,
    by rw [syms]; exact i.symbol, ?_, ?_, ?_, ?_⟩
  · rw [mem.wordsVal h.zero_apart (by have := h.low K.zero (by simp); omega_arith), i.zero]
  · intro j hj
    rw [mem.byte (fun w hw => .inr (by have := bounded w hw; omega_arith)) (by omega_arith), i.bits j hj]
  · rw [params _ (by simp), i.coeffA]
  · rw [params _ (by simp), i.coeffB]
where
  bounded' : ∀ w ∈ loopWrites K, w.1 + w.2 ≤ 8192 := fun w hw => by
    have := h.loop_bounded w hw; omega

/-! ## The start -/

/-- `a` and `3b` to the point functions' slots, `R = S`, and `r31 = J`. -/
theorem start_ok (K : TCombCfg) {s : State} {base : Addr} (h : Layout K) (hw : WsReg s base)
    (hx : K.start.1 < 2 ^ (64 * K.L.M.n)) (hy : K.start.2 < 2 ^ (64 * K.L.M.n))
    (hz : K.one < 2 ^ (64 * K.L.M.n)) (hJ : K.J < 2 ^ 15) :
    WP isa (.block (ladderSetup K.L ++ Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.x K.start.1 ++
      Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.y K.start.2 ++
      Impl.Mont.PPC64LE.setConst K.L.M.n K.L.R.z K.one ++ ([.li .r31 K.J] : List Instr))) s fun t =>
      Kp [.r4, .r11, .r31] s t ∧ Unch base (writes K) s.mem t.mem ∧ CpOk K.L base t.mem s.mem ∧
      t.gpr .r31 = BitVec.ofNat 64 K.J ∧
      wordsVal t.mem base K.L.R.x K.L.M.n = K.start.1 ∧ wordsVal t.mem base K.L.R.y K.L.M.n = K.start.2 ∧
      wordsVal t.mem base K.L.R.z K.L.M.n = K.one := by
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  obtain ⟨rx, ry, rz, -, -⟩ := low
  obtain ⟨rxy, rxz, ryz⟩ := h.point.rne
  have nowrap := hw.nowrap
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine wp_append (WP.mono (ladderSetup_ok hw h.point) fun u ⟨ku, ou, cp⟩ => ?_)
  have wu := hw.of_kp ku
  refine wp_append (WP.mono (setConstW_ok wu (o := K.L.R.x) (by omega_arith) hx) fun v ⟨ov, xv, kv⟩ => ?_)
  have wv := wu.of_kp kv
  refine wp_append (WP.mono (setConstW_ok wv (o := K.L.R.y) (by omega_arith) hy) fun a ⟨oa, ya, ka⟩ => ?_)
  have wa := wv.of_kp ka
  refine wp_append (WP.mono (setConstW_ok wa (o := K.L.R.z) (by omega_arith) hz) fun b ⟨ob, zb, kb⟩ => ?_)
  refine wp_step (exec_li hJ) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, ite_true]
  have ub : Unch base [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n)] u.mem b.mem :=
    ov.unch.trans (oa.unch.trans ob.unch)
  refine ⟨((ku.mono (by decide)).trans ((kv.mono (by decide)).trans ((ka.mono (by decide)).trans
      (kb.mono (by decide))))).trans (Kp.write _ _ (by decide)), ?_, ?_, trivial, ?_, ?_, zb⟩
  · apply (ou.trans ub).mono
    intro w hw'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | (rfl | rfl | rfl) <;> simp [writes]
  · apply cp.keep h.point.k3 h.point.k6 ub
    intro w hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl <;> (left; dsimp only; omega_arith)
  · rw [ob.wordsVal (by omega_arith) (by omega_arith), oa.wordsVal (by omega_arith) (by omega_arith), xv]
  · rw [ob.wordsVal (by omega_arith) (by omega_arith), ya]


/-! ## The signed entry -/

theorem q_lay {K : TCombCfg} (h : Layout K) :
    oAt K.L.M.n + 48 * K.L.M.n = K.Q.x ∧ K.Q.y = K.Q.x + 8 * K.L.M.n ∧ K.Q.z = K.Q.x + 16 * K.L.M.n ∧
      K.Q.x + 24 * K.L.M.n = aAt K.L.M.n ∧ aAt K.L.M.n + 16 * K.L.M.n + 64 + 48 * K.L.M.n = own K.L.M.n ∧
      own K.L.M.n + 64 * K.L.M.n = 4096 ∧ b3At K.L.M.n = aAt K.L.M.n + 8 * K.L.M.n ∧
      ownAt K.L.M.n = aAt K.L.M.n + 16 * K.L.M.n ∧ K.Q.x % 4 = 0 := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, ho, -, h8⟩ := lay_nums h.point.k3 h.point.k6
  simp only [TCombCfg.Q, ptAt]
  omega

/-- `y = -y` if the digit is negative: `-y` by the field's subtraction from
zero, then the selection by the sign's mask. -/
theorem negate_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} (positive : Prop) [Decidable positive]
    (h : Layout K) (hw : WsReg s base) (hm : K.F.m = m) (hn : K.F.k = K.L.M.n) (hM : ModOk K.L.M.n m)
    (hz : wordsVal s.mem base K.zero K.L.M.n = 0) (hy : wordsVal s.mem base K.Q.y K.L.M.n < m)
    (hmask : ∀ u, Rk fnClob s u → Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem u.mem →
      WP isa K.signMask u fun v =>
        v.gpr .r10 = (if positive then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r6, .r10] u v ∧ v.mem = u.mem) :
    WP isa (.seq (subCall K.F K.neg K.zero K.Q.y) (.seq K.signMask (.block (sel K.L.M.n K.Q.y K.Q.y K.neg)))) s
      fun t =>
      Rk fnClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      wordsVal t.mem base K.Q.x K.L.M.n = wordsVal s.mem base K.Q.x K.L.M.n ∧
      wordsVal t.mem base K.Q.y K.L.M.n =
        (if positive then wordsVal s.mem base K.Q.y K.L.M.n else (m - wordsVal s.mem base K.Q.y K.L.M.n) % m) ∧
      wordsVal t.mem base K.Q.z K.L.M.n = wordsVal s.mem base K.Q.z K.L.M.n := by
  obtain ⟨hqx, hqy, hqz, hqa, hown, hown', -, -, hq4⟩ := q_lay h
  have := lay_nums h.point.k3 h.point.k6
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low
  obtain ⟨rx, ry, rz, hzero, hneg⟩ := low
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
    (by omega) (by omega) h.al.2 (by omega) (by omega) (by omega) (.inl (Nat.le_refl _))
    (.inr (by omega))) fun t ⟨yt, kt, ot⟩ => ?_
  have qold : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    rw [mv]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply ou.wordsVal _ (by rcases hx with rfl | rfl | rfl <;> omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rcases hx with rfl | rfl | rfl <;> exact ⟨.inr (by omega), .inl (by omega)⟩
  refine ⟨(ku.rk).trans ((kv.rk (by decide)).trans (kt.rk (by decide))), ?_, ?_, ?_, ?_, ?_⟩
  · have ov : Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] s.mem v.mem := by rw [mv]; exact ou
    apply (ov.trans ot.unch).cover
    intro w hw'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with (rfl | rfl) | rfl
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(ownAt K.L.M.n, 4096 - ownAt K.L.M.n), by simp [loopWrites], by dsimp only; omega,
        by dsimp only; omega⟩
    · exact ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], by dsimp only; omega, by dsimp only; omega⟩
  · intro x hx
    have lowx : x + 8 * K.L.M.n ≤ oAt K.L.M.n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have negx := h.negApart x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp)
    rw [ot.wordsVal (.inl (by omega)) (by omega), mv]
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

/-- The entry of digit `j`, signed, in the point functions' `Q`. -/
theorem entry_ok (K : TCombCfg) {C : Curve} {tbl : List (List (Nat × Nat))} {start : Nat × Nat}
    (h : Config K C tbl start) (hC : Law C) {s : State} {base T : Addr} {k j : Nat}
    (i : CurveInputs K C tbl base T k s) (hj : j < K.J) (hk : k < 2 ^ K.L.nbits)
    (gj : s.gpr .r31 = BitVec.ofNat 64 j)
    (hd : Region.Disjoint ⟨T, 8 * (tableWords K C tbl).length⟩ ⟨base, 8192⟩) :
    WP isa K.entry s fun t =>
      Rk fnClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n) ∧
      (∀ x ∈ [K.Q.x, K.Q.y, K.Q.z], wordsVal t.mem base x K.L.M.n < C.p) ∧
      Rep C (tmv C K.L.M.n base t K.Q.x) (tmv C K.L.M.n base t K.Q.y) (tmv C K.L.M.n base t K.Q.z)
        (signedPtW C K.w k j) := by
  unfold TCombCfg.entry
  have hp : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  have hfit : C.p ≤ 2 ^ (64 * K.L.M.n) := Nat.le_of_lt h.modulus.m_lt
  have hl := lay_nums h.layout.point.k3 h.layout.point.k6
  obtain ⟨hqx, hqy, hqz, hqa, hown, hown', -, -, hq4⟩ := q_lay h.layout
  have lo := h.layout.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lo
  obtain ⟨rx, ry, rz, zlo, nlo⟩ := lo
  have hbits := h.layout.point.bitsE
  have hb4 := h.layout.point.bits
  have nowrap := i.wsr.nowrap
  have hH15 : K.H + 1 ≤ 2 ^ 15 := by
    have := h.row
    have := Nat.le_mul_of_pos_left K.H (show 0 < 16 * K.L.M.n by have := h.layout.point.k3; omega)
    omega
  refine WP.seq (WP.mono_syms (digit_ok K i.wsr.ws i.wsr.at3 h.w9 hj h.J15 h.startBits h.coverBits h.bitsOff
    hbits hk gj i.bits) fun u ⟨gu, ku, mu⟩ syu => ?_)
  have iu : CurveInputs K C tbl base T k u :=
    i.keep h.layout hd (ku.rk (rs' := fnClob)) (by decide) (by rw [mu]; exact Unch.refl _ _ _) syu
  refine WP.seq (WP.mono_syms (selectTable_ok K (a := magH K.H (combWin K.w k j)) iu.wsr hq4 h.layout.al.1
    (by omega) (by omega) (.inl (by omega)) (Nat.lt_of_lt_of_le h.one_lt hfit) iu.zero
    (by have := h.layout.point.k3; omega) hH15 h.row (h.magnitude k j) gu
    (by rw [ku.g]; exact gj) iu.table iu.symbol h.tables.len h.tables.lenH hj (by have := h.J15; omega) hp hfit hd)
    fun v ⟨xv, yv, zv, kv, ov⟩ syv => ?_)
  have ouv : Unch base (loopWrites K) u.mem v.mem :=
    ov.unch.cover fun w hw' => by
      rw [List.mem_singleton] at hw'; subst hw'
      exact ⟨(oAt K.L.M.n, 72 * K.L.M.n), by simp [loopWrites], by dsimp only; omega, by dsimp only; omega⟩
  have iv : CurveInputs K C tbl base T k v := iu.keep h.layout hd kv (by decide) ouv syv
  have ylt : wordsVal v.mem base K.Q.y K.L.M.n < C.p := by
    rw [yv]; split
    · exact h.one_lt
    · exact Nat.mod_lt _ hp
  have oldR : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z],
      wordsVal v.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    have lowx : x + 8 * K.L.M.n ≤ oAt K.L.M.n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    rw [ov.wordsVal (.inl (by omega)) (by omega), mu]
  have mask : ∀ a, Rk fnClob v a → Unch base [(K.neg, 8 * K.L.M.n), (own K.L.M.n, 64 * K.L.M.n)] v.mem a.mem →
      WP isa K.signMask a fun b =>
        b.gpr .r10 = (if K.H ≤ combWin K.w k j then 0 else BitVec.allOnes 64) ∧ Kp [.r4, .r6, .r10] a b ∧
          b.mem = a.mem := by
    intro a ka ma
    have wa := iv.wsr.of_rk ka
    refine WP.mono (signMask_ok K wa.ws wa.at3 ⟨h.w1, h.w9⟩ hj h.J15 h.startBits h.coverBits h.bitsOff hbits hk
      (by rw [ka.g, kv.g, ku.g]; exact gj) fun b hb => ?_) fun t ⟨v', k', m'⟩ => ⟨v', k', m'⟩
    rw [ma.byte (fun w hw' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl <;> (right; dsimp only; omega)) (by omega), iv.bits b hb]
  refine WP.mono (negate_ok K (K.H ≤ combWin K.w k j) h.layout iv.wsr h.fieldM h.fieldK h.modulus iv.zero ylt mask)
    fun t ⟨kt, ot, rt, xt, yt, zt⟩ => ?_
  refine ⟨((ku.rk (rs' := fnClob)).trans ((kv.mono (by decide)).trans kt)), ?_,
    fun x hx => (rt x hx).trans (oldR x hx), ?_, ?_⟩
  · have ou : Unch base (loopWrites K) s.mem u.mem := by rw [mu]; exact Unch.refl _ _ _
    exact (ou.trans (ouv.trans ot)).cover fun w hw' => ⟨w, by
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

/-- `ptCall_ok`, for the functions of `S` of `n`-word coordinates modulo `m`. -/
theorem ptCallAt_ok {S : Impl.Weierstrass.Mont.Modulus} {n m : Nat} [NeZero m] (hk : S.k = n) (hm : S.m = m)
    (hM : ModOk n m) (hodd : m % 2 = 1) (hk3 : 3 ≤ n) (hk6 : n ≤ 6) (dbl : Bool) {a0 : Bool} {s : State}
    {base : Addr} (hw : WsReg s base) (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc n dbl x) n < m) :
    WP isa (ptCall S dbl a0) s fun s' => Rk fnClob s s' ∧
      Outs base [(oAt n, 3 * elemBytes n), (ownAt n, 4096 - ownAt n)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc n dbl j) n < m) ∧
      (Eb n m dbl s'.mem base 0, Eb n m dbl s'.mem base 1, Eb n m dbl s'.mem base 2) =
        ptVal a0 dbl (Eb n m dbl s.mem base) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hk hm
  subst hk hm
  exact ptCall_ok hM hodd hk3 hk6 dbl hw hlt

/-- `R = R + Q` by a call of the complete addition. -/
theorem add_ok (K : TCombCfg) {s : State} {base : Addr} {m : Nat} [NeZero m]
    (h : Layout K) (hw : WsReg s base) (hm : K.F.m = m) (hn : K.F.k = K.L.M.n) (hM : ModOk K.L.M.n m)
    (hodd : m % 2 = 1)
    (hlt : ∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.Q.x, K.Q.y, K.Q.z, aAt K.L.M.n, b3At K.L.M.n],
      wordsVal s.mem base x K.L.M.n < m) :
    WP isa K.add s fun t =>
      Rk fnClob s t ∧ Unch base (loopWrites K) s.mem t.mem ∧
      (∀ x ∈ [K.L.R.x, K.L.R.y, K.L.R.z], wordsVal t.mem base x K.L.M.n < m) ∧
      (toM m (2 ^ (64 * K.L.M.n)) (wordsVal t.mem base K.L.R.x K.L.M.n),
       toM m (2 ^ (64 * K.L.M.n)) (wordsVal t.mem base K.L.R.y K.L.M.n),
       toM m (2 ^ (64 * K.L.M.n)) (wordsVal t.mem base K.L.R.z K.L.M.n)) =
        rcbAdd (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base (aAt K.L.M.n) K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base (b3At K.L.M.n) K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.L.R.x K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.L.R.y K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.L.R.z K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.Q.x K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.Q.y K.L.M.n))
          (toM m (2 ^ (64 * K.L.M.n)) (wordsVal s.mem base K.Q.z K.L.M.n)) := by
  unfold TCombCfg.add
  have hk3 := h.point.k3
  have hk6 := h.point.k6
  obtain ⟨h1, h2, he, hb3', ha', hq', hp', ho', -, -⟩ := lay_nums hk3 hk6
  obtain ⟨hqx, hqy, hqz, hqa, hown, hown', hb3, hoA, hq4⟩ := q_lay h
  have low := h.low
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at low hlt
  obtain ⟨rx, ry, rz, -, -⟩ := low
  obtain ⟨lx, ly, lz, lqx, lqy, lqz, la, lb⟩ := hlt
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := h.point.al
  have nowrap := hw.nowrap
  have cp := copyPt_conds (a := K.L.R) hk3 hk6 (.inl rfl) (by omega) (by omega) (by omega) ⟨rxl, ryl, rzl⟩
  refine WP.seq (WP.mono (copyPt_ok hw.ws hw.at3 (n := K.L.M.n) (o := K.P) (a := K.L.R)
    cp.1 cp.2.1 cp.2.2.1 cp.2.2.2) fun u ⟨px, py, pz, ku, outs⟩ => ?_)
  simp only [P_eq] at px py pz outs
  have wu := hw.of_kp ku
  have other : ∀ x ∈ [K.Q.x, K.Q.y, K.Q.z, aAt K.L.M.n, b3At K.L.M.n],
      wordsVal u.mem base x K.L.M.n = wordsVal s.mem base x K.L.M.n := by
    intro x hx
    have U : Unch base [(pAt K.L.M.n, 8 * K.L.M.n), (pAt K.L.M.n + elemBytes K.L.M.n, 8 * K.L.M.n),
      (pAt K.L.M.n + 2 * elemBytes K.L.M.n, 8 * K.L.M.n)] s.mem u.mem := outs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    apply U.wordsVal _ (by rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> (refine ⟨.inr ?_, .inr ?_, .inr ?_⟩ <;> omega)
  have hltu : ∀ x ∈ rIds, wordsVal u.mem base (enc K.L.M.n false x) K.L.M.n < m := by
    apply rIds_lt_of false
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    refine ⟨by rw [px]; exact lx, by rw [py]; exact ly, by rw [pz]; exact lz, ?_, ?_, ?_, ?_, ?_⟩
    · have e := other K.Q.x (by simp); rw [Q_eq] at e; rw [e]; exact lqx
    · have e := other K.Q.y (by simp); rw [Q_eq] at e; rw [e]; exact lqy
    · have e := other K.Q.z (by simp); rw [Q_eq] at e; rw [e]; exact lqz
    · rw [other _ (by simp)]; exact la
    · rw [other _ (by simp)]; exact lb
  refine WP.seq (WP.mono (ptCallAt_ok (S := K.F) (a0 := false) hn hm hM hodd hk3 hk6 false wu hltu)
    fun v ⟨kv, ov, lv, eqv⟩ => ?_)
  have wv := wu.of_rk kv
  have cO := copyPt_conds (a := K.L.R) hk3 hk6 (.inl rfl) (by omega) (by omega) (by omega) ⟨rxl, ryl, rzl⟩
  have backIn : ∀ d ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.O.x, K.O.y, K.O.z], d + 8 * K.L.M.n ≤ 8192 := by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega
  have back4 : ∀ d ∈ [K.L.R.x, K.L.R.y, K.L.R.z, K.O.x, K.O.y, K.O.z], d % 4 = 0 := by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, elemBytes]
    omega
  have backApart : ∀ d ∈ [K.L.R.x, K.L.R.y, K.L.R.z], ∀ e ∈ [K.O.x, K.O.y, K.O.z],
      d + 8 * K.L.M.n ≤ e ∨ e + 8 * K.L.M.n ≤ d := by
    simp only [O_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    omega
  refine WP.mono (copyPt_ok wv.ws wv.at3 (n := K.L.M.n) (o := K.L.R) (a := K.O) back4 backIn h.point.rne
    backApart) fun t ⟨tx, ty, tz, kt, ot⟩ => ?_
  refine ⟨((ku.rk (by decide)).trans (kv.trans (kt.rk (by decide)))), ?_, ?_, ?_⟩
  · have U₁ : Unch base [(pAt K.L.M.n, 8 * K.L.M.n), (pAt K.L.M.n + elemBytes K.L.M.n, 8 * K.L.M.n),
      (pAt K.L.M.n + 2 * elemBytes K.L.M.n, 8 * K.L.M.n)] s.mem u.mem := outs
    have U₂ : Unch base [(oAt K.L.M.n, 3 * elemBytes K.L.M.n), (ownAt K.L.M.n, 4096 - ownAt K.L.M.n)]
      u.mem v.mem := ov
    have U₃ : Unch base [(K.L.R.x, 8 * K.L.M.n), (K.L.R.y, 8 * K.L.M.n), (K.L.R.z, 8 * K.L.M.n)]
      v.mem t.mem := ot
    apply (U₁.trans (U₂.trans U₃)).cover
    intro w hw'
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'
    have mO : (oAt K.L.M.n, 72 * K.L.M.n) ∈ loopWrites K := by simp [loopWrites]
    have mW : (ownAt K.L.M.n, 4096 - ownAt K.L.M.n) ∈ loopWrites K := by simp [loopWrites]
    rcases hw' with (rfl | rfl | rfl) | (rfl | rfl) | (rfl | rfl | rfl)
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mO, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, mW, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by simp [loopWrites], Nat.le_refl _, Nat.le_refl _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    have l0 := lv 0 (by decide)
    have l1 := lv 1 (by decide)
    have l2 := lv 2 (by decide)
    rw [enc_0] at l0
    rw [enc_1] at l1
    rw [enc_2] at l2
    rw [tx, ty, tz, O_eq]
    exact ⟨l0, l1, l2⟩
  · rw [tx, ty, tz]
    simp only [Eb, enc_0, enc_1, enc_2] at eqv
    simp only [O_eq]
    rw [eqv]
    simp only [ptVal, Eb, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10, Bool.false_eq_true, ↓reduceIte]
    rw [px, py, pz]
    have oa := other (aAt K.L.M.n) (by simp)
    have ob := other (b3At K.L.M.n) (by simp)
    have ox := other K.Q.x (by simp)
    have oy := other K.Q.y (by simp)
    have oz := other K.Q.z (by simp)
    rw [Q_eq] at ox oy oz
    dsimp only at ox oy oz
    rw [Q_eq]
    dsimp only
    rw [oa, ob, ox, oy, oz]

end VG.Proof.Weierstrass.PPC64LE.TComb
