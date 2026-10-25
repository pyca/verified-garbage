module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSqStart
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: a squaring's masks

`sqMasks_ok`: `ok`, `done` and whether `y := x`, from `k < t`, `k + 1 = t`,
`done`, `x = 1` and `x = -1`, as `sqStep` has them.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (sqMasks nArr sTc sK sDone sOk sLive sE1 sE2)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The top bit of `a - b`: `a < b`. -/
theorem lt64 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = b64 (decide (a < b)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega_arith), Nat.mod_eq_of_lt (a := b) (by omega_arith)]
  by_cases h : a < b
  · simp only [h, decide_true, b2n, ite_true]; omega_arith
  · simp only [h, decide_false, b2n, Bool.false_eq_true, ite_false]; omega_arith

/-- The top bit of `(a + 1 xor b) - 1`: `a + 1 = b`. -/
theorem eq64 {a b : Nat} (ha : a + 1 < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a + 1#64 ^^^ BitVec.ofNat 64 b) - 1#64) >>> 63 = b64 (decide (a + 1 = b)) := by
  have e : BitVec.ofNat 64 a + 1#64 = BitVec.ofNat 64 (a + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  rw [e]
  have hx : (BitVec.ofNat 64 (a + 1) ^^^ BitVec.ofNat 64 b).toNat = (a + 1) ^^^ b := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a + 1) (by omega_arith),
      Nat.mod_eq_of_lt (a := b) (by omega_arith)]
  have hlt : (a + 1) ^^^ b < 2 ^ 63 := Nat.xor_lt_two_pow ha hb
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, hx,
    show (1#64).toNat = 1 from rfl, BitVec.toNat_ofNat]
  by_cases h : a + 1 = b
  · subst h; rw [Nat.xor_self]; simp [b2n]
  · have hne : BitVec.ofNat 64 (a + 1) ^^^ BitVec.ofNat 64 b ≠ 0#64 := fun h' => h (by
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h')
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a + 1) (by omega_arith),
        Nat.mod_eq_of_lt (a := b) (by omega_arith)] at this
      exact this)
    have : (a + 1) ^^^ b ≠ 0 := fun h' => hne (BitVec.eq_of_toNat_eq (by rw [hx, h']; rfl))
    simp only [h, decide_false, b2n, Bool.false_eq_true, ite_false]
    omega_arith

/-- The masks of a squaring, on words. -/
theorem masks64 (a q done ok e1 e2 : Bool) :
    let L := b64 a &&& (b64 done ^^^ 1#64)
    let S := b64 q ||| b64 e2
    (b64 ok ||| L &&& b64 e1) = b64 (ok || (!done && a && e1)) ∧
      (b64 done ||| (b64 e1 ||| S) &&& L) = b64 (done || (!done && a && (e1 || (e2 || q)))) ∧
      (((b64 e1 ||| S) &&& L ^^^ 1#64) &&& L) = b64 (!done && a && !e1 && !(e2 || q)) := by
  cases a <;> cases q <;> cases done <;> cases ok <;> cases e1 <;> cases e2 <;> decide

theorem mk1 (a done ok e1 : Bool) :
    (b64 ok ||| b64 a &&& (b64 done ^^^ 1#64) &&& b64 e1) = b64 (ok || (!done && a && e1)) := by
  cases a <;> cases done <;> cases ok <;> cases e1 <;> decide

theorem mk2 (a q done e1 e2 : Bool) :
    (b64 done ||| (b64 e1 ||| (b64 q ||| b64 e2)) &&& (b64 a &&& (b64 done ^^^ 1#64))) =
      b64 (done || (!done && a && (e1 || (e2 || q)))) := by
  cases a <;> cases q <;> cases done <;> cases e1 <;> cases e2 <;> decide

theorem mk3 (a q done e1 e2 : Bool) :
    (((b64 e1 ||| (b64 q ||| b64 e2)) &&& (b64 a &&& (b64 done ^^^ 1#64)) ^^^ 1#64) &&&
      (b64 a &&& (b64 done ^^^ 1#64))) = b64 (!done && a && !e1 && !(e2 || q)) := by
  cases a <;> cases q <;> cases done <;> cases e1 <;> cases e2 <;> decide

/-- `sqMasks`: `ok`, `done` and `live` (whether `y := x`) of `sqStep`. -/
theorem sqMasks_ok {s0 u : State} (w : Ws u (rvB s0) (rvZ s0) (ww (kK s0)) nArr) {k t : Nat} {done ok e1 e2 : Bool}
    (hK : slot u.mem (rvB s0) sK = k) (hT : slot u.mem (rvB s0) sTc = t)
    (hD : slot u.mem (rvB s0) sDone = b2n done) (hO : slot u.mem (rvB s0) sOk = b2n ok)
    (h1 : slot u.mem (rvB s0) sE1 = b2n e1) (h2 : slot u.mem (rvB s0) sE2 = b2n e2)
    (hk : k + 1 < 2 ^ 63) (ht : t < 2 ^ 63) :
    WP isa (.block sqMasks) u fun v => v.mem =
      ((u.mem.writeW (off (rvB s0) sOk) (BitVec.ofNat 32 (b2n (ok || (!done && decide (k < t) && e1))))).writeW
        (off (rvB s0) sDone)
          (BitVec.ofNat 32 (b2n (done || (!done && decide (k < t) && (e1 || (e2 || decide (k + 1 = t)))))))).writeW
        (off (rvB s0) sLive)
          (BitVec.ofNat 32 (b2n (!done && decide (k < t) && !e1 && !(e2 || decide (k + 1 = t))))) ∧
      Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8] u v := by
  have hz : 160 ≤ rvZ s0 := w.hdr_le
  have L := lt64 (a := k) (b := t) (by omega_arith) ht
  have E := eq64 (a := k) (b := t) hk ht
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8] (Q := fun x => x.mem =
    ((u.mem.writeW (rvB s0 + BitVec.ofNat 64 sOk)
              (BitVec.setWidth 32
                (BitVec.ofNat 64 (b2n ok) |||
                  (BitVec.ofNat 64 k - BitVec.ofNat 64 t) >>> 63 &&& (BitVec.ofNat 64 (b2n done) ^^^ 1#64) &&&
                    BitVec.ofNat 64 (b2n e1)))).writeW
          (rvB s0 + BitVec.ofNat 64 sDone)
          (BitVec.setWidth 32
            (BitVec.ofNat 64 (b2n done) |||
              (BitVec.ofNat 64 (b2n e1) |||
                  (((BitVec.ofNat 64 k + 1#64 ^^^ BitVec.ofNat 64 t) - 1#64) >>> 63 ||| BitVec.ofNat 64 (b2n e2))) &&&
                ((BitVec.ofNat 64 k - BitVec.ofNat 64 t) >>> 63 &&& (BitVec.ofNat 64 (b2n done) ^^^ 1#64))))).writeW
      (rvB s0 + BitVec.ofNat 64 sLive)
      (BitVec.setWidth 32
        (((BitVec.ofNat 64 (b2n e1) |||
                (((BitVec.ofNat 64 k + 1#64 ^^^ BitVec.ofNat 64 t) - 1#64) >>> 63 ||| BitVec.ofNat 64 (b2n e2))) &&&
              ((BitVec.ofNat 64 k - BitVec.ofNat 64 t) >>> 63 &&& (BitVec.ofNat 64 (b2n done) ^^^ 1#64)) ^^^
            1#64) &&&
          ((BitVec.ofNat 64 k - BitVec.ofNat 64 t) >>> 63 &&& (BitVec.ofNat 64 (b2n done) ^^^ 1#64)))))
    ?_ (by decide)) fun v ⟨m, kv⟩ => ⟨?_, kv⟩
  · prun [sqMasks, w.r31, w.scr.ld (show sK + 4 ≤ rvZ s0 by simp only [sK]; omega_arith),
      w.scr.ld (show sTc + 4 ≤ rvZ s0 by simp only [sTc]; omega_arith),
      w.scr.ld (show sDone + 4 ≤ rvZ s0 by simp only [sDone]; omega_arith),
      w.scr.ld (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega_arith),
      w.scr.ld (show sE1 + 4 ≤ rvZ s0 by simp only [sE1]; omega_arith),
      w.scr.ld (show sE2 + 4 ≤ rvZ s0 by simp only [sE2]; omega_arith),
      w.scr.st (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega_arith),
      w.scr.st (show sDone + 4 ≤ rvZ s0 by simp only [sDone]; omega_arith),
      w.scr.st (show sLive + 4 ≤ rvZ s0 by simp only [sLive]; omega_arith),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sK < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sTc < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sDone < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sE1 < 2 ^ 15 by decide),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sE2 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sDone < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sLive < 2 ^ 15 by decide),
      ld_slot hK, ld_slot hT, ld_slot hD, ld_slot hO, ld_slot h1, ld_slot h2]
  · rw [m, L, E]
    rw [show BitVec.ofNat 64 (b2n ok) = b64 ok from rfl, show BitVec.ofNat 64 (b2n done) = b64 done from rfl,
      show BitVec.ofNat 64 (b2n e1) = b64 e1 from rfl, show BitVec.ofNat 64 (b2n e2) = b64 e2 from rfl,
      mk1, mk2, mk3, b64_w32, b64_w32, b64_w32]

end VG.Proof.Rsa.PPC64LE.Recover
