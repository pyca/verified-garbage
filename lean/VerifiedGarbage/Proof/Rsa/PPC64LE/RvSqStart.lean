module

import VerifiedGarbage.Proof.Rsa.PPC64LE.RvExp
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet

/-!
# `vg_rsa_recover_primes` on PPC64LE: the start of the squarings

`y = 1` and `y = -1` (`eqS`), and `sqInit`: the squarings' stage `SI s0 j 0`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (sqInit mY aO aNg nArr sTc sK sDone sOk sE1 sE2)
open VG.Impl.Rsa.PPC64LE.Keys (seqs eqS)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A slot apart from a store. -/
theorem slot_wne (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) : slot (m.writeW (off B d) v) B e = slot m B e := by
  simp only [slot, w32, off]
  rw [Mem.readW_writeW_sep (Offset.sep B (h.symm) he hd) (by decide)]

/-- A slot loaded. -/
theorem ld_slot {m : Mem} {B : Addr} {d v : Nat} (h : slot m B d = v) :
    (m.readW (B + BitVec.ofNat 64 d) 32).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have := (m.readW (B + BitVec.ofNat 64 d) 32).isLt
  simp only [slot, w32, off] at h
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), h]
  rw [← h]; omega_arith

/-- A flag as a word. -/
abbrev b64 (b : Bool) : BitVec 64 := BitVec.ofNat 64 (b2n b)

theorem b64_or (a b : Bool) : b64 a ||| b64 b = b64 (a || b) := by cases a <;> cases b <;> decide

theorem b64_w32 (b : Bool) : (b64 b).setWidth 32 = BitVec.ofNat 32 (b2n b) := by cases b <;> decide

theorem b2n_ite (p : Prop) [Decidable p] : (if p then 1 else 0) = b2n (decide p) := by
  by_cases h : p <;> simp [h, b2n]

/-- `y` of the candidate `j`. -/
abbrev y0 (s0 : State) (j : Nat) : Nat := Spec.Rsa.powMod (j + 2) (rR s0) (nV s0)

/-- The squarings' state after `k`. -/
abbrev sqst (s0 : State) (j k : Nat) : Nat × Bool × Bool := sqIter (nV s0) (tT s0) k (sqStart (nV s0) (y0 s0 j))

/-- The squarings for the candidate `j` after `k`. -/
structure SI (s0 : State) (j k : Nat) (u : State) : Prop where
  cf : CF s0 u
  r24 : u.gpr .r24 = BitVec.ofNat 64 j
  vY : num u.mem (rvB s0) (ww (kK s0)) mY = (sqst s0 j k).1 * RR s0 % nV s0
  done : slot u.mem (rvB s0) sDone = b2n (sqst s0 j k).2.1
  ok : slot u.mem (rvB s0) sOk = b2n (sqst s0 j k).2.2
  sk : slot u.mem (rvB s0) sK = k

/-- `y = ±1`, and the squarings started. -/
theorem sqStart_ok {s0 u : State} (hn : NOk s0) {j : Nat} (h : EI s0 j (cB s0) u) (hr : rR s0 < 2 ^ cB s0) :
    WP isa (seqs [eqS sE1 mY aO, eqS sE2 mY aNg, .block sqInit]) u fun t =>
      SI s0 j 0 t ∧ t.gpr .r27 = BitVec.ofNat 64 (cB s0) := by
  have c := h.cf
  have hz : 160 ≤ rvZ s0 := c.ws.hdr_le
  have hn0 : 0 < nV s0 := by have := hn.big; omega_arith
  have hn1 : 1 < nV s0 := by have := hn.big; omega_arith
  have ex : y0 s0 j < nV s0 := by rw [y0, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hn0
  have eY : num u.mem (rvB s0) (ww (kK s0)) mY = y0 s0 j * RR s0 % nV s0 := by
    rw [h.vY, Nat.mod_eq_of_lt hr, y0, VG.Proof.Bignum.powMod_eq, Nat.mod_mul_mod]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok c.ws (d := sE1) (a := mY) (b := aO) (by decide) (by decide) (by decide) (by decide))
    fun u1 ⟨ws1, kk1, e1, k1⟩ => ?_
  have c1 := c.of_keep kk1 (by simp) (by decide) k1 ws1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok ws1 (d := sE2) (a := mY) (b := aNg) (by decide) (by decide) (by decide) (by decide))
    fun u2 ⟨ws2, kk2, e2, k2⟩ => ?_
  have c2 := c1.of_keep kk2 (by simp) (by decide) k2 ws2
  have Y1 : num u1.mem (rvB s0) (ww (kK s0)) mY = num u.mem (rvB s0) (ww (kK s0)) mY :=
    kk1.num (by simp) (by decide) (c.ws.fit64 (by decide))
  rw [eY, c.vO, b2n_ite, show decide (y0 s0 j * RR s0 % nV s0 = RR s0 % nV s0) = decide (y0 s0 j = 1) from
    decide_eq_decide.mpr (eq_one_mont hn.coprime hn1 ex rfl)] at e1
  rw [Y1, eY, c1.vNg, b2n_ite, show decide (y0 s0 j * RR s0 % nV s0 = nV s0 - RR s0 % nV s0) =
    decide (y0 s0 j = nV s0 - 1) from decide_eq_decide.mpr (eq_neg_mont hn.coprime hn1 ex rfl)] at e2
  have e1' : slot u2.mem (rvB s0) sE1 = b2n (decide (y0 s0 j = 1)) := by
    rw [kk2.slot (e := sE1) (by decide) (by decide), e1]
  rw [show seqs [Code.block sqInit] = .block sqInit from rfl]
  refine WP.mono (WP.keep [.r0, .r3, .r27] (Q := fun x => x.mem =
    ((u2.mem.writeW (off (rvB s0) sDone) ((b64 (decide (y0 s0 j = 1) || decide (y0 s0 j = nV s0 - 1))).setWidth 32)).writeW
      (off (rvB s0) sOk) ((0#64).setWidth 32)).writeW (off (rvB s0) sK) ((0#64).setWidth 32) ∧
    x.gpr .r27 = u2.gpr .r26) ?_
    (by decide)) fun t ⟨⟨mt, a27⟩, kt⟩ => ?_
  · prun [sqInit, ws2.r31, ws2.scr.ld (show sE1 + 4 ≤ rvZ s0 by simp only [sE1]; omega_arith),
      ws2.scr.ld (show sE2 + 4 ≤ rvZ s0 by simp only [sE2]; omega_arith),
      ws2.scr.st (show sDone + 4 ≤ rvZ s0 by simp only [sDone]; omega_arith),
      ws2.scr.st (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega_arith),
      ws2.scr.st (show sK + 4 ≤ rvZ s0 by simp only [sK]; omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sE1 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sE2 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sDone < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sK < 2 ^ 15 by decide),
      ld_slot e1', ld_slot e2, b64_or, BitVec.add_zero]
  have kk : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sDone, sOk, sK] u2.mem t.mem := by
    rw [mt]
    exact KeyWorkspace.Keep.trans (keep_slot _ _ (by simp) (by decide)) (KeyWorkspace.Keep.trans
      (keep_slot _ _ (by simp) (by decide)) (keep_slot _ _ (by simp) (by decide)))
  have ct := c2.of_keep kk (by simp) (by decide) kt (ws2.of_keep kt)
  refine ⟨⟨ct, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kt.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]; exact h.r24
  · rw [kk.num (by simp) (by decide) (c.ws.fit64 (by decide)), kk2.num (by simp) (by decide) (c.ws.fit64 (by decide)),
      Y1, eY]; rfl
  · rw [mt, slot_wne _ _ _ (by decide) (by decide) (by decide), slot_wne _ _ _ (by decide) (by decide) (by decide),
      slot_write_self, b64_w32, BitVec.toNat_ofNat]
    simp only [sqst, sqIter, sqStart]
    have := b2n_le (decide (y0 s0 j = 1) || decide (y0 s0 j = nV s0 - 1)); omega_arith
  · rw [mt, slot_wne _ _ _ (by decide) (by decide) (by decide), slot_write_self]; rfl
  · rw [mt, slot_write_self]; rfl
  · rw [a27]; exact c2.r26

end VG.Proof.Rsa.PPC64LE.Recover
