module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvMul
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFlags
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_recover_primes` on PPC64LE: a bit of `m`

`bitHead_ok`: the top bit of the digit's register `sWord`, which is shifted
left; `bit_ok`: a step of the shared model (`Fused.step`) by that bit, from
`BI s0 j st` to `BI s0 j (Fused.step n g bit st)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (bit bitHead flags multiply mmul mBase mY mG mXm mX aT aRoot aO aNg nArr
  sWord sDone sOk sBit sLive sE1 sE2 iX iY)
open VG.Impl.Rsa.PPC64LE.Keys (seqs eqS sel copy)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `bitHead`: the top bit of `sWord` into `sBit`, and `sWord` shifted. -/
theorem bitHead_ok {s0 u : State} (w : Ws u (rvB s0) (rvZ s0) (ww (kK s0)) nArr) {W : Nat}
    (hW : slot u.mem (rvB s0) sWord = W) :
    WP isa (.block bitHead) u fun v => KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sBit, sWord] u.mem v.mem ∧
      slot v.mem (rvB s0) sBit = W / 2 ^ 31 ∧ slot v.mem (rvB s0) sWord = W * 2 % 2 ^ 32 ∧
      Keep [.r0, .r3] u v := by
  have hz : 160 ≤ rvZ s0 := w.hdr_le
  have Wl : W < 2 ^ 32 := by rw [← hW]; exact (u.mem.readW _ 32).isLt
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun x => x.mem =
    (u.mem.writeW (off (rvB s0) sBit) ((BitVec.ofNat 64 W >>> 31).setWidth 32)).writeW (off (rvB s0) sWord)
      ((BitVec.ofNat 64 W <<< 1).setWidth 32)) ?_ (by decide)) fun v ⟨m, kv⟩ => ⟨?_, ?_, ?_, kv⟩
  · prun [bitHead, w.r31, w.scr.ld (show sWord + 4 ≤ rvZ s0 by simp only [sWord]; omega),
      w.scr.st (show sBit + 4 ≤ rvZ s0 by simp only [sBit]; omega),
      w.scr.st (show sWord + 4 ≤ rvZ s0 by simp only [sWord]; omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sWord < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sBit < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sWord < 2 ^ 15 by decide), ld_slot hW]
  · rw [m]
    exact KeyWorkspace.Keep.trans (keep_slot _ _ (by simp) (by decide)) (keep_slot _ _ (by simp) (by decide))
  · rw [m, slot_wne _ _ _ (by decide) (by decide) (by decide), slot_write_self, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  · rw [m, slot_write_self, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := W) (by omega), Nat.mod_mod_of_dvd _ (by decide)]

/-- The flags after a bit, as `Fused.step` has them. -/
theorem step_ok_flag (bit done ok e1 : Bool) :
    ((ok || (!bit && !done && e1)) && !bit) = ((ok || (!done && e1 && !bit)) && !bit) := by
  cases bit <;> cases done <;> cases ok <;> cases e1 <;> rfl

/-- A bit. -/
theorem bit_ok {s0 u : State} (hn : NOk s0) {j : Nat} (hj : j < 100) {st : Fused.State} {W : Nat}
    (h : BI s0 j st u) (hW : slot u.mem (rvB s0) sWord = W) :
    WP isa bit u fun t => BI s0 j (Fused.step (nV s0) (j + 2) (decide (W / 2 ^ 31 = 1)) st) t ∧
      slot t.mem (rvB s0) sWord = W * 2 % 2 ^ 32 ∧ t.gpr .r28 = u.gpr .r28 - BitVec.ofNat 64 1 ∧
      t.gpr .r27 = u.gpr .r27 := by
  have c := h.cf
  have hz : 160 ≤ rvZ s0 := c.ws.hdr_le
  have hn0 : 0 < nV s0 := by have := hn.big; omega
  have hn1 : 1 < nV s0 := by have := hn.big; omega
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => c.ws.fit64 hj
  have Wl : W < 2 ^ 32 := by rw [← hW]; exact (u.mem.readW _ 32).isLt
  have vl : st.value < nV s0 := h.bnd.1
  generalize hb : decide (W / 2 ^ 31 = 1) = b
  have bW : W / 2 ^ 31 = b2n b := by rw [← hb]; by_cases e : W / 2 ^ 31 = 1 <;> simp [e, b2n] <;> omega
  have Yl : num u.mem (rvB s0) (ww (kK s0)) mY < nV s0 := by rw [h.vY]; exact Nat.mod_lt _ hn0
  unfold bit
  simp only [List.cons_append, List.nil_append]
  -- The bit.
  rw [wp_seqs_cons (by simp [mmul])]
  refine WP.mono (bitHead_ok c.ws hW) fun u1 ⟨kk1, b1, w1, k1⟩ => ?_
  have c1 := c.of_keep kk1 (by simp) (by decide) k1 (c.ws.of_keep k1)
  -- `x = y²`.
  rw [wp_seqs_append (by simp [mmul]) (List.cons_ne_nil _ _)]
  have Y1 : num u1.mem (rvB s0) (ww (kK s0)) mY = st.value * RR s0 % nV s0 := by
    rw [kk1.num (by simp) (by decide) (fit mY (by decide))]; exact h.vY
  have Yl1 : num u1.mem (rvB s0) (ww (kK s0)) mY < nV s0 := by rw [Y1]; exact Nat.mod_lt _ hn0
  refine WP.mono (mmul_ok c1.base c1.ws (o := iX) (a := iY) (b := iY) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c1.r12 c1.inv
    (by rw [c1.vMN]; change lowV u1.mem s0 mY < _; rw [low_of_lt Yl1]; exact Yl1))
    fun u2 ⟨_, ws2, kk2, lt2, eq2, k2⟩ => ?_
  have c2 := c1.of_keep kk2 (by decide) (by simp) k2 ws2
  change num u2.mem (rvB s0) (ww (kK s0)) mX < lowV u1.mem s0 mBase at lt2
  change num u2.mem (rvB s0) (ww (kK s0)) mX * RR s0 % lowV u1.mem s0 mBase =
    lowV u1.mem s0 mY * lowV u1.mem s0 mY % lowV u1.mem s0 mBase at eq2
  rw [c1.vMN, low_of_lt Yl1, Y1, ← mont_sq_eq] at eq2
  rw [c1.vMN] at lt2
  have X2 : num u2.mem (rvB s0) (ww (kK s0)) mX = st.value * st.value % nV s0 * RR s0 % nV s0 := by
    have := VG.Proof.Bignum.mont_cancel hn.coprime eq2
    rwa [Nat.mod_eq_of_lt lt2, Nat.mod_mod] at this
  generalize hx : st.value * st.value % nV s0 = x at X2
  have xl : x < nV s0 := by rw [← hx]; exact Nat.mod_lt _ hn0
  -- `x g`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have r24 : u2.gpr .r24 = BitVec.ofNat 64 j := by
    rw [k2.gpr _ (by decide), k1.gpr _ (by decide)]; exact h.r24
  have G2 : num u2.mem (rvB s0) (ww (kK s0)) mG = (j + 2) * RR s0 % nV s0 := by
    rw [kk2.num (by decide) (by simp) (fit mG (by decide)), kk1.num (by simp) (by decide) (fit mG (by decide))]
    exact h.vG
  refine WP.mono (multiply_ok hn c2 r24 hj X2 G2) fun u3 ⟨c3, kk3, M3, k3⟩ => ?_
  have X3 : num u3.mem (rvB s0) (ww (kK s0)) mX = x * RR s0 % nV s0 := by
    rw [kk3.num (by decide) (by decide) (fit mX (by decide))]; exact X2
  -- The new `y`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have b3 : slot u3.mem (rvB s0) sBit = b2n b := by
    rw [kk3.slot (e := sBit) (by decide) (by decide), kk2.slot (e := sBit) (by decide) (by simp), b1, bW]
  refine WP.mono (sel_ok c3.ws (o := aT) (a := mX) (b := mXm) (sl := sBit) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [b3]; exact b2n_le _)) fun u4 ⟨ws4, kk4, T4, k4⟩ => ?_
  have c4 := c3.of_keep kk4 (by decide) (by simp) k4 ws4
  have vT : num u4.mem (rvB s0) (ww (kK s0)) aT =
      (Fused.step (nV s0) (j + 2) b st).value * RR s0 % nV s0 := by
    rw [T4, b3, X3, M3, Fused.step_value, hx]
    cases b <;> rfl
  have vl' : (Fused.step (nV s0) (j + 2) b st).value < nV s0 := Fused.step_lt _ _ _ _ hn0
  generalize hv : (Fused.step (nV s0) (j + 2) b st).value = v at vT vl'
  -- `y = ±1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok ws4 (d := sE1) (a := aT) (b := aO) (by decide) (by decide) (by decide) (by decide))
    fun u5 ⟨ws5, kk5, e5, k5⟩ => ?_
  have c5 := c4.of_keep kk5 (by simp) (by decide) k5 ws5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok ws5 (d := sE2) (a := aT) (b := aNg) (by decide) (by decide) (by decide) (by decide))
    fun u6 ⟨ws6, kk6, e6, k6⟩ => ?_
  have c6 := c5.of_keep kk6 (by simp) (by decide) k6 ws6
  have T5 : num u5.mem (rvB s0) (ww (kK s0)) aT = num u4.mem (rvB s0) (ww (kK s0)) aT :=
    kk5.num (by simp) (by decide) (fit aT (by decide))
  rw [vT, c4.vO, b2n_ite, show decide (v * RR s0 % nV s0 = RR s0 % nV s0) = decide (v = 1) from
    decide_eq_decide.mpr (eq_one_mont hn.coprime hn1 vl' rfl)] at e5
  rw [T5, vT, c5.vNg, b2n_ite, show decide (v * RR s0 % nV s0 = nV s0 - RR s0 % nV s0) = decide (v = nV s0 - 1) from
    decide_eq_decide.mpr (eq_neg_mont hn.coprime hn1 vl' rfl)] at e6
  -- The flags.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have sl6 : ∀ e ∈ [sBit, sDone, sOk], slot u6.mem (rvB s0) e = slot u3.mem (rvB s0) e := by
    intro e he
    have h4 : e + 4 ≤ KeyWorkspace.hdr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> decide
    have d1 : ∀ d ∈ [sE1], e + 4 ≤ d ∨ d + 4 ≤ e := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> decide
    have d2 : ∀ d ∈ [sE2], e + 4 ≤ d ∨ d + 4 ≤ e := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> decide
    rw [kk6.slot h4 d2, kk5.slot h4 d1, kk4.slot h4 (by simp)]
  have sl3 : ∀ e ∈ [sDone, sOk], slot u3.mem (rvB s0) e = slot u.mem (rvB s0) e := by
    intro e he
    have h4 : e + 4 ≤ KeyWorkspace.hdr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> decide
    have d1 : ∀ d ∈ [sBit, sWord], e + 4 ≤ d ∨ d + 4 ≤ e := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> decide
    have d3 : ∀ d ∈ [VG.Impl.Rsa.PPC64LE.Keys.sC], e + 4 ≤ d ∨ d + 4 ≤ e := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> decide
    rw [kk3.slot h4 d3, kk2.slot h4 (by simp), kk1.slot h4 d1]
  refine WP.mono (flags_ok ws6 (bit := b) (done := st.done) (ok := st.root.isSome) (e1 := decide (v = 1))
    (e2 := decide (v = nV s0 - 1)) (by rw [sl6 sBit (by simp)]; exact b3)
    (by rw [sl6 sDone (by simp), sl3 sDone (by simp)]; exact h.done)
    (by rw [sl6 sOk (by simp), sl3 sOk (by simp)]; exact h.ok)
    (by rw [kk6.slot (e := sE1) (by decide) (by decide)]; exact e5) e6) fun u7 ⟨m7, k7⟩ => ?_
  have kk7 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sLive, sOk, sDone] u6.mem u7.mem := by
    rw [m7]
    exact KeyWorkspace.Keep.trans (keep_slot _ _ (by simp) (by decide)) (KeyWorkspace.Keep.trans
      (keep_slot _ _ (by simp) (by decide)) (keep_slot _ _ (by simp) (by decide)))
  have ws7 := ws6.of_keep k7
  have c7 := c6.of_keep kk7 (by simp) (by decide) k7 ws7
  have live7 : slot u7.mem (rvB s0) sLive = b2n (!b && !st.done && decide (v = 1)) := by
    rw [m7, slot_wne _ _ _ (by decide) (by decide) (by decide), slot_wne _ _ _ (by decide) (by decide) (by decide),
      slot_write_self, BitVec.toNat_ofNat]
    have := b2n_le (!b && !st.done && decide (v = 1)); omega
  -- The root.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_self_ok ws7 (o := aRoot) (b := mY) (sl := sLive) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [live7]; exact b2n_le _)) fun u8 ⟨ws8, kk8, R8, k8⟩ => ?_
  have c8 := c7.of_keep kk8 (by decide) (by simp) k8 ws8
  -- `y :=` the new `y`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws8 (o := mY) (a := aT) (by decide) (by decide) (by decide) (by decide))
    fun u9 ⟨ws9, kk9, Y9, k9, _⟩ => ?_
  have c9 := c8.of_keep kk9 (by decide) (by simp) k9 ws9
  -- The count.
  rw [show seqs [Code.block [Instr.subi .r28 .r28 1]] = .block [.subi .r28 .r28 1] from rfl]
  refine WP.mono (WP.keep [.r28] (Q := fun x => x.gpr .r28 = u9.gpr .r28 - BitVec.ofNat 64 1 ∧ x.mem = u9.mem)
    (by prun) (by decide)) fun t ⟨⟨a28, mt⟩, kt⟩ => ?_
  have kkt : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [] u9.mem t.mem := by
    rw [mt]; exact KeyWorkspace.Keep.refl _ _ _ _ _
  have ct := c9.of_keep kkt (by simp) (by simp) kt (c9.ws.of_keep kt)
  -- What the steps kept.
  have K9 : ∀ r ∈ [Reg.r24, .r27, .r28], u9.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
    rw [k9.gpr _ (by decide), k8.gpr _ (by decide), k7.gpr _ (by decide), k6.gpr _ (by decide),
      k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  have Y7 : num u7.mem (rvB s0) (ww (kK s0)) mY = st.value * RR s0 % nV s0 := by
    rw [kk7.num (by simp) (by decide) (fit mY (by decide)), kk6.num (by simp) (by decide) (fit mY (by decide)),
      kk5.num (by simp) (by decide) (fit mY (by decide)), kk4.num (by decide) (by simp) (fit mY (by decide)),
      kk3.num (by decide) (by decide) (fit mY (by decide)), kk2.num (by decide) (by simp) (fit mY (by decide))]
    exact Y1
  have R7 : num u7.mem (rvB s0) (ww (kK s0)) aRoot = num u.mem (rvB s0) (ww (kK s0)) aRoot := by
    rw [kk7.num (by simp) (by decide) (fit aRoot (by decide)), kk6.num (by simp) (by decide) (fit aRoot (by decide)),
      kk5.num (by simp) (by decide) (fit aRoot (by decide)), kk4.num (by decide) (by simp) (fit aRoot (by decide)),
      kk3.num (by decide) (by decide) (fit aRoot (by decide)), kk2.num (by decide) (by simp) (fit aRoot (by decide)),
      kk1.num (by simp) (by decide) (fit aRoot (by decide))]
  have Rt : num t.mem (rvB s0) (ww (kK s0)) aRoot =
      if b2n (!b && !st.done && decide (v = 1)) = 0 then num u.mem (rvB s0) (ww (kK s0)) aRoot
      else st.value * RR s0 % nV s0 := by
    rw [mt, kk9.num (by decide) (by simp) (fit aRoot (by decide)), R8, live7, R7, Y7]
  have sl9 : ∀ e ∈ [sOk, sDone, sWord], slot t.mem (rvB s0) e = slot u7.mem (rvB s0) e := by
    intro e he
    have h4 : e + 4 ≤ KeyWorkspace.hdr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> decide
    rw [mt, kk9.slot h4 (by simp), kk8.slot h4 (by simp)]
  have e7 : ∀ e ∈ [sWord], slot u7.mem (rvB s0) e = slot u1.mem (rvB s0) e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    rw [kk7.slot (e := sWord) (by decide) (by decide), kk6.slot (e := sWord) (by decide) (by decide),
      kk5.slot (e := sWord) (by decide) (by decide), kk4.slot (e := sWord) (by decide) (by simp),
      kk3.slot (e := sWord) (by decide) (by decide), kk2.slot (e := sWord) (by decide) (by simp)]
  have ev : b = false → v = x := fun e => by
    subst e; rw [← hv, Fused.step_value]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hx
  refine ⟨⟨ct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Fused.bounded_step hn0 h.bnd⟩, ?_, ?_, ?_⟩
  · rw [kt.gpr _ (by decide), K9 _ (by simp)]; exact h.r24
  · rw [mt, Y9, kk8.num (by decide) (by simp) (fit aT (by decide)), kk7.num (by simp) (by decide) (fit aT (by decide)),
      kk6.num (by simp) (by decide) (fit aT (by decide)), T5, vT, ← hv]
  · rw [mt, kk9.num (by decide) (by simp) (fit mG (by decide)), kk8.num (by decide) (by simp) (fit mG (by decide)),
      kk7.num (by simp) (by decide) (fit mG (by decide)), kk6.num (by simp) (by decide) (fit mG (by decide)),
      kk5.num (by simp) (by decide) (fit mG (by decide)), kk4.num (by decide) (by simp) (fit mG (by decide)),
      kk3.num (by decide) (by decide) (fit mG (by decide)), G2]
  · intro y hy
    rw [Fused.step_root, hx] at hy
    rw [Rt]
    cases b
    · rw [← ev rfl] at hy
      simp only [Bool.false_eq_true, ↓reduceIte] at hy
      by_cases e : (!st.done && decide (v = 1)) = true
      · rw [ite_eq_left e] at hy
        cases hy
        have e' : (!false && !st.done && decide (v = 1)) = true := by simpa using e
        rw [e', show b2n true = 1 from rfl, ite_eq_right (by decide)]
      · rw [ite_eq_right e] at hy
        have e' : (!false && !st.done && decide (v = 1)) = false := by simpa using e
        rw [e', show b2n false = 0 from rfl, ite_eq_left rfl]
        exact h.vRoot y hy
    · simp at hy
  · rw [Rt]
    split
    · exact h.rootLt
    · exact Nat.mod_lt _ hn0
  · rw [sl9 sOk (by simp), m7, slot_wne _ _ _ (by decide) (by decide) (by decide), slot_write_self,
      BitVec.toNat_ofNat, (Fused.step_flags (nV s0) (j + 2) b st).2, hx, step_ok_flag]
    have := b2n_le ((st.root.isSome || (!st.done && decide (v = 1) && !b)) && !b)
    rw [Nat.mod_eq_of_lt (by omega)]
    cases b
    · rw [ev rfl]
    · simp
  · rw [sl9 sDone (by simp), m7, slot_write_self, BitVec.toNat_ofNat, (Fused.step_flags (nV s0) (j + 2) b st).1,
      hx, hv]
    have := b2n_le (st.done && !b || decide (v = 1) || decide (v = nV s0 - 1))
    rw [Nat.mod_eq_of_lt (by omega)]
    cases b
    · rw [ev rfl]; simp
    · simp
  · rw [sl9 sWord (by simp), e7 sWord (by simp), w1]
  · rw [a28, K9 _ (by simp)]
  · rw [kt.gpr _ (by decide), K9 _ (by simp)]

end VG.Proof.Rsa.PPC64LE.Recover
