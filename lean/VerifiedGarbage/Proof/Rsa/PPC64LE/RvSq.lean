module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSqMasks
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: the squarings

`sqBody_ok`: a squaring under the masks, `sqStep` (from `SI s0 j k` to
`SI s0 j (k + 1)`), and `sqLoop_ok`: all `c` of them.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (sqBody sqLoop sqMasks sqNext mmul mBase mY mX aO aNg aU nArr sTc sK sDone sOk
  sLive sE1 sE2 iX iY)
open VG.Impl.Rsa.PPC64LE.Keys (seqs eqS)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A squaring. -/
theorem sqBody_ok {s0 u : State} (hn : NOk s0) {j k : Nat} (h : SI s0 j k u) (hk : k < 2 ^ 31)
    (ht : tT s0 < 2 ^ 31) :
    WP isa sqBody u fun v => SI s0 j (k + 1) v ∧ v.gpr .r27 = u.gpr .r27 - BitVec.ofNat 64 1 := by
  have c := h.cf
  have hz : 160 ≤ rvZ s0 := c.ws.hdr_le
  have hn0 : 0 < nV s0 := by have := hn.big; omega_arith
  have hn1 : 1 < nV s0 := by have := hn.big; omega_arith
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => c.ws.fit64 hj
  have ex : y0 s0 j < nV s0 := by rw [y0, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hn0
  have hy : (sqst s0 j k).1 < nV s0 := sqIter_lt hn0 k _ ex
  have hvY := h.vY; have hdn := h.done; have hok := h.ok
  generalize hst : sqst s0 j k = st at hvY hdn hok hy
  obtain ⟨y, done, ok⟩ := st
  have Yl : num u.mem (rvB s0) (ww (kK s0)) mY < nV s0 := by rw [hvY]; exact Nat.mod_lt _ hn0
  unfold sqBody
  -- `X = y² R`.
  rw [wp_seqs_append (by simp [mmul]) (List.cons_ne_nil _ _)]
  refine WP.mono (mmul_ok c.base c.ws (o := iX) (a := iY) (b := iY) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c.r12 c.inv
    (by rw [c.vMN]; change lowV u.mem s0 mY < _; rw [low_of_lt Yl]; exact Yl))
    fun u1 ⟨_, ws1, kk1, lt1, eq1, k1⟩ => ?_
  have c1 := c.of_keep kk1 (by decide) (by simp) k1 ws1
  change num u1.mem (rvB s0) (ww (kK s0)) mX < lowV u.mem s0 mBase at lt1
  change num u1.mem (rvB s0) (ww (kK s0)) mX * RR s0 % lowV u.mem s0 mBase =
    lowV u.mem s0 mY * lowV u.mem s0 mY % lowV u.mem s0 mBase at eq1
  rw [c.vMN, low_of_lt Yl, hvY, ← mont_sq_eq] at eq1
  rw [c.vMN] at lt1
  have X1 : num u1.mem (rvB s0) (ww (kK s0)) mX = y * y % nV s0 * RR s0 % nV s0 := by
    have := VG.Proof.Bignum.mont_cancel hn.coprime eq1
    rwa [Nat.mod_eq_of_lt lt1, Nat.mod_mod] at this
  have hx : y * y % nV s0 < nV s0 := Nat.mod_lt _ hn0
  -- `x = ±1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok ws1 (d := sE1) (a := mX) (b := aO) (by decide) (by decide) (by decide) (by decide))
    fun u2 ⟨ws2, kk2, e1, k2⟩ => ?_
  have c2 := c1.of_keep kk2 (by simp) (by decide) k2 ws2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok ws2 (d := sE2) (a := mX) (b := aNg) (by decide) (by decide) (by decide) (by decide))
    fun u3 ⟨ws3, kk3, e2, k3⟩ => ?_
  have c3 := c2.of_keep kk3 (by simp) (by decide) k3 ws3
  have X2 : num u2.mem (rvB s0) (ww (kK s0)) mX = num u1.mem (rvB s0) (ww (kK s0)) mX :=
    kk2.num (by simp) (by decide) (fit mX (by decide))
  rw [X1, c1.vO, b2n_ite, show decide (y * y % nV s0 * RR s0 % nV s0 = RR s0 % nV s0) =
    decide (y * y % nV s0 = 1) from decide_eq_decide.mpr (eq_one_mont hn.coprime hn1 hx rfl)] at e1
  rw [X2, X1, c2.vNg, b2n_ite, show decide (y * y % nV s0 * RR s0 % nV s0 = nV s0 - RR s0 % nV s0) =
    decide (y * y % nV s0 = nV s0 - 1) from decide_eq_decide.mpr (eq_neg_mont hn.coprime hn1 hx rfl)] at e2
  have sl3 : ∀ e ∈ [sK, sTc, sDone, sOk], slot u3.mem (rvB s0) e = slot u.mem (rvB s0) e := by
    intro e he
    have h4 : e + 4 ≤ KeyWorkspace.hdr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    have d2 : ∀ d ∈ [sE2], e + 4 ≤ d ∨ d + 4 ≤ e := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    have d1 : ∀ d ∈ [sE1], e + 4 ≤ d ∨ d + 4 ≤ e := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> decide
    rw [kk3.slot h4 d2, kk2.slot h4 d1, kk1.slot h4 (by simp)]
  -- The masks.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hT : slot u3.mem (rvB s0) sTc = tT s0 := by rw [sl3 sTc (by simp)]; exact c.vT
  refine WP.mono (sqMasks_ok ws3 (k := k) (t := tT s0) (done := done) (ok := ok)
    (e1 := decide (y * y % nV s0 = 1)) (e2 := decide (y * y % nV s0 = nV s0 - 1))
    (by rw [sl3 sK (by simp)]; exact h.sk) hT (by rw [sl3 sDone (by simp)]; exact hdn)
    (by rw [sl3 sOk (by simp)]; exact hok)
    (by rw [kk3.slot (e := sE1) (by decide) (by decide)]; exact e1) e2 (by omega_arith) (by omega_arith))
    fun u4 ⟨m4, k4⟩ => ?_
  have kk4 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sOk, sDone, sLive] u3.mem u4.mem := by
    rw [m4]
    exact KeyWorkspace.Keep.trans (keep_slot _ _ (by simp) (by decide)) (KeyWorkspace.Keep.trans
      (keep_slot _ _ (by simp) (by decide)) (keep_slot _ _ (by simp) (by decide)))
  have ws4 := ws3.of_keep k4
  have c4 := c3.of_keep kk4 (by simp) (by decide) k4 ws4
  -- `y := x` if live.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws4 (o := aU) (a := mY) (by decide) (by decide) (by decide) (by decide))
    fun u5 ⟨ws5, kk5, v5, k5, _⟩ => ?_
  have c5 := c4.of_keep kk5 (by decide) (by simp) k5 ws5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have live5 : slot u5.mem (rvB s0) sLive = b2n (!done && decide (k < tT s0) && !decide (y * y % nV s0 = 1) &&
      !(decide (y * y % nV s0 = nV s0 - 1) || decide (k + 1 = tT s0))) := by
    rw [kk5.slot (e := sLive) (by decide) (by simp), m4, slot_write_self, BitVec.toNat_ofNat]
    have := b2n_le (!done && decide (k < tT s0) && !decide (y * y % nV s0 = 1) &&
      !(decide (y * y % nV s0 = nV s0 - 1) || decide (k + 1 = tT s0))); omega_arith
  refine WP.mono (sel_ok ws5 (o := mY) (a := aU) (b := mX) (sl := sLive) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [live5]; exact b2n_le _)) fun u6 ⟨ws6, kk6, v6, k6⟩ => ?_
  have c6 := c5.of_keep kk6 (by decide) (by simp) k6 ws6
  -- `k += 1`.
  rw [show seqs [Code.block sqNext] = .block sqNext from rfl]
  have sK6 : slot u6.mem (rvB s0) sK = k := by
    rw [kk6.slot (e := sK) (by decide) (by simp), kk5.slot (e := sK) (by decide) (by simp),
      kk4.slot (e := sK) (by decide) (by decide), sl3 sK (by simp)]; exact h.sk
  refine WP.mono (WP.keep [.r3, .r27] (Q := fun x =>
    x.mem = u6.mem.writeW (off (rvB s0) sK) ((BitVec.ofNat 64 k + 1#64).setWidth 32) ∧
      x.gpr .r27 = u6.gpr .r27 - 1#64) ?_ (by decide))
    fun t ⟨⟨mt, a27⟩, kt⟩ => ?_
  · prun [sqNext, ws6.r31, ws6.scr.ld (show sK + 4 ≤ rvZ s0 by simp only [sK]; omega_arith),
      ws6.scr.st (show sK + 4 ≤ rvZ s0 by simp only [sK]; omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sK < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sK < 2 ^ 15 by decide), ld_slot sK6]
  have kkt : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sK] u6.mem t.mem := by
    rw [mt]; exact keep_slot _ _ (by simp) (by decide)
  have ct := c6.of_keep kkt (by simp) (by decide) kt (ws6.of_keep kt)
  have r24 : t.gpr .r24 = u.gpr .r24 := by
    rw [kt.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide),
      k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]
  have r27 : u6.gpr .r27 = u.gpr .r27 := by
    rw [k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide),
      k2.gpr _ (by decide), k1.gpr _ (by decide)]
  have Y6 : num u6.mem (rvB s0) (ww (kK s0)) mY =
      if b2n (!done && decide (k < tT s0) && !decide (y * y % nV s0 = 1) &&
        !(decide (y * y % nV s0 = nV s0 - 1) || decide (k + 1 = tT s0))) = 0 then y * RR s0 % nV s0
      else y * y % nV s0 * RR s0 % nV s0 := by
    rw [v6, live5, v5, kk4.num (by simp) (by decide) (fit mY (by decide)),
      kk3.num (by simp) (by decide) (fit mY (by decide)), kk2.num (by simp) (by decide) (fit mY (by decide)),
      kk1.num (by decide) (by simp) (fit mY (by decide)), hvY,
      kk5.num (by decide) (by simp) (fit mX (by decide)), kk4.num (by simp) (by decide) (fit mX (by decide)),
      kk3.num (by simp) (by decide) (fit mX (by decide)), X2, X1]
  have e : sqst s0 j (k + 1) = sqStep (nV s0) (tT s0) k (y, done, ok) := by
    show sqStep (nV s0) (tT s0) k (sqst s0 j k) = _; rw [hst]
  refine ⟨⟨ct, by rw [r24]; exact h.r24, ?_, ?_, ?_, ?_⟩, by rw [a27, r27]⟩
  · rw [kkt.num (by simp) (by decide) (fit mY (by decide)), Y6, e]
    simp only [sqStep]
    generalize (!done && decide (k < tT s0) && !decide (y * y % nV s0 = 1) &&
      !(decide (y * y % nV s0 = nV s0 - 1) || decide (k + 1 = tT s0))) = L
    cases L <;> simp [b2n]
  · rw [mt, slot_wne _ _ _ (by decide) (by decide) (by decide), kk6.slot (e := sDone) (by decide) (by simp),
      kk5.slot (e := sDone) (by decide) (by simp), m4, slot_wne _ _ _ (by decide) (by decide) (by decide),
      slot_write_self, BitVec.toNat_ofNat, e]
    simp only [sqStep]
    have := b2n_le (done || (!done && decide (k < tT s0) && (decide (y * y % nV s0 = 1) ||
      (decide (y * y % nV s0 = nV s0 - 1) || decide (k + 1 = tT s0)))))
    rw [Nat.mod_eq_of_lt (by omega_arith)]
  · rw [mt, slot_wne _ _ _ (by decide) (by decide) (by decide), kk6.slot (e := sOk) (by decide) (by simp),
      kk5.slot (e := sOk) (by decide) (by simp), m4, slot_wne _ _ _ (by decide) (by decide) (by decide),
      slot_wne _ _ _ (by decide) (by decide) (by decide), slot_write_self, BitVec.toNat_ofNat, e]
    simp only [sqStep]
    have := b2n_le (ok || (!done && decide (k < tT s0) && decide (y * y % nV s0 = 1)))
    rw [Nat.mod_eq_of_lt (by omega_arith)]
  · rw [mt, slot_write_self, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [BitVec.toNat_ofNat]
    omega_arith

/-- The `c` squarings. -/
theorem sqLoop_ok {s0 u : State} (hn : NOk s0) {j : Nat} (h : SI s0 j 0 u)
    (h27 : u.gpr .r27 = BitVec.ofNat 64 (cB s0)) (hc0 : 0 < cB s0) (hc : cB s0 < 2 ^ 31) (ht : tT s0 < 2 ^ 31) :
    WP isa sqLoop u (SI s0 j (cB s0)) :=
  wp_countdown (body := sqBody) (cnt := .r27) (N := cB s0) (by omega_arith) hc0 (SI s0 j)
    (fun _ hk _ e _ => sqBody_ok hn e (by omega_arith) ht) h h27

end VG.Proof.Rsa.PPC64LE.Recover
