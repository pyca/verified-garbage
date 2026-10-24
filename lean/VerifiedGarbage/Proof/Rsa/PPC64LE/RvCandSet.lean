module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCtx
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: a candidate set up

`candSet_ok` and the product after it: for the candidate `j` (`g = j + 2`),
`y = R mod n` (1 in Montgomery form), `g R mod n`, `r`'s copy and the count
of its bits: `EI s0 j 0`, the exponentiation's stage after 0 bits.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (candSet mmul mBase mR2 mY mG aN aOne aZ aO nArr iG iR2 wR wRc)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `t` and `r` of `m = 2^t r`. -/
abbrev tT (s0 : State) : Nat := (Spec.Rsa.splitTwos (mV s0)).1
abbrev rR (s0 : State) : Nat := (Spec.Rsa.splitTwos (mV s0)).2

/-- The exponentiation for the candidate `j` after `i` bits: `y = g^(r mod 2^i)`
and `g^(2^i)` in Montgomery form, and `r / 2^i` in `r`'s copy. -/
structure EI (s0 : State) (j i : Nat) (u : State) : Prop where
  cf : CF s0 u
  r24 : u.gpr .r24 = BitVec.ofNat 64 j
  vY : num u.mem (rvB s0) (ww (kK s0)) mY = (j + 2) ^ (rR s0 % 2 ^ i) * RR s0 % nV s0
  vG : num u.mem (rvB s0) (ww (kK s0)) mG = (j + 2) ^ (2 ^ i) * RR s0 % nV s0
  vRc : num u.mem (rvB s0) (wW (kK s0)) wRc = rR s0 / 2 ^ i

/-- The modulus is odd and at least 2. -/
structure NOk (s0 : State) : Prop where
  odd : nV s0 % 2 = 1
  big : 128 ≤ nV s0

theorem NOk.of_valid {s0 : State} (h : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) : NOk s0 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, Nat.le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ 511 by decide)) h.1.1.2⟩

theorem NOk.coprime {s0 : State} (h : NOk s0) : Nat.Coprime (RR s0) (nV s0) :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

/-- A number below `n` is its low digits. -/
theorem low_of_lt {m : Mem} {s0 : State} {j : Nat} (h : num m (rvB s0) (ww (kK s0)) j < nV s0) :
    lowV m s0 j = num m (rvB s0) (ww (kK s0)) j :=
  low_eq (Nat.lt_trans h nV_lt)

theorem ofNat_add2 (j : Nat) :
    (BitVec.ofNat 64 j + BitVec.ofNat 64 2).setWidth 32 = BitVec.ofNat 32 (j + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem arrW (w j : Nat) : arr (2 * w + 2) j = arr w (2 * j) := by
  simp only [arr, S]; grind

theorem arrW_end (w j : Nat) : arr w (2 * j) + 4 * (2 * w + 2) ≤ arr w (2 * j + 2) := by
  simp only [arr, S]; grind

/-- A number of the `W` view kept by a step on other key arrays. -/
theorem keepW_num {s0 : State} {js : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) js [] m m') {j : Nat} (hj : ∀ i ∈ js, i < 2 * j ∨ 2 * j + 2 ≤ i)
    (hf : arr (ww (kK s0)) (2 * j + 2) ≤ 2 ^ 64) :
    num m' (rvB s0) (wW (kK s0)) j = num m (rvB s0) (wW (kK s0)) j := by
  have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
  have e2 := arrW_end (ww (kK s0)) j
  change val32 m' (rvB s0) (arr (wW (kK s0)) j) (wW (kK s0)) = val32 m (rvB s0) (arr (wW (kK s0)) j) (wW (kK s0))
  rw [hW, arrW]
  exact keep_apart k (fun i hi => arr_apart (hj i hi) (Nat.le_refl _) e2) (by simp) (Nat.le_trans e2 hf)

/-- `candSet` and `g := g R² R⁻¹`. -/
theorem cand0_ok {s0 u : State} (h : CF s0 u) (hn : NOk s0) {j : Nat} (hj : j < 100)
    (h24 : u.gpr .r24 = BitVec.ofNat 64 j) :
    WP isa (seqs ([candSet] ++ mmul iG iG iR2)) u fun t => EI s0 j 0 t ∧ t.gpr .r27 = BitVec.ofNat 64 (cB s0) := by
  have z := h.base.sz
  have w1 := z.w1; have w2 := z.w2; have svW := z.svW; have svZ := z.svZ; have svw := z.svw
  have hww : ww (kK s0) = 2 * wm (kK s0) + 2 := rfl
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => h.ws.fit64 hj
  rw [wp_seqs_append (List.cons_ne_nil _ _) (by simp [mmul]), show seqs [candSet] = candSet from rfl]
  unfold candSet
  -- `[mG] := 0`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := mG) (a := aZ) (by decide) (by decide) (by decide) (by decide))
    fun u1 ⟨ws1, kk1, v1, k1, _⟩ => ?_
  have c1 := h.of_keep kk1 (by decide) (by simp) k1 ws1
  have z1 : num u1.mem (rvB s0) (ww (kK s0)) mG = 0 := by
    rw [v1]; exact val32_zeros fun i hi => h.zZ i (by omega)
  -- Its low digit `:= g`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil ([Instr.addi .r0 .r24 2, .store .w .r0 .r5 0]),
    ← List.append_assoc]
  refine lowOp_ok (f := fun _ => BitVec.ofNat 32 (j + 2)) ws1 (j := mG) (by decide) (by decide)
    (fun v v5 vm kv => ?_) fun u2 ws2 kk2 v2 k2 _ => WP.block_nil ?_
  · refine WP.mono (WP.keep [.r0] ?_ (by decide)) fun u' ⟨m, k⟩ => ⟨m, k.mono⟩
    have e24 : v.gpr .r24 = BitVec.ofNat 64 j := by rw [kv.gpr _ (by decide), k1.gpr _ (by decide)]; exact h24
    prun [v5, vm, e24, (ws1.scr.congr kv.wr).st (show arr (ww (kK s0)) mG + 4 ≤ rvZ s0 by
      have := ws1.arr_fit (j := mG) (by decide); simp only [S] at this; omega), ofNat_add2 j]
  have c2 := c1.of_keep kk2 (by decide) (by simp) k2 ws2
  have g2 : num u2.mem (rvB s0) (ww (kK s0)) mG = j + 2 := by
    rw [v2, z1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- `y := 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws2 (o := mY) (a := aO) (by decide) (by decide) (by decide) (by decide))
    fun u3 ⟨ws3, kk3, v3, k3, _⟩ => ?_
  have c3 := c2.of_keep kk3 (by decide) (by simp) k3 ws3
  -- `r`'s copy.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil VG.Impl.Rsa.PPC64LE.Recover.ctxW]
  refine ctxW_ok ws3 (by omega) (Nat.le_trans svW (Nat.le_trans (Nat.le_add_right _ _) svZ))
    fun u4 ws4 m4 k4 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws4 (o := wRc) (a := wR) (by decide) (by decide) (by decide) (by decide))
    fun u5 ⟨ws5, kk5, v5, k5, _⟩ => ?_
  rw [show seqs [Code.block (VG.Impl.Rsa.PPC64LE.Recover.ctxw ++ [.addi .r27 .r26 0])] =
    .block (VG.Impl.Rsa.PPC64LE.Recover.ctxw ++ [.addi .r27 .r26 0]) from rfl]
  refine ctxw_ok ws5 (by omega) (by rw [← svw]; omega) fun u6 ws6 m6 k6 => ?_
  refine WP.mono (WP.keep [.r27] (Q := fun x => x.gpr .r27 = u6.gpr .r26 ∧ x.mem = u6.mem) (by prun [BitVec.add_zero])
    (by decide)) fun u7 ⟨⟨a27, m7⟩, k7⟩ => ?_
  have kk5' : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [30, 31] [] u3.mem u7.mem := by
    rw [m7, m6, ← m4]; exact keepW_key kk5
  have ws7 : Ws u7 (rvB s0) (rvZ s0) (ww (kK s0)) nArr := ws6.of_keep k7
  have K : Keep (.r27 :: .r29 :: .r30 :: opRegs) u3 u7 := (((k4.trans k5).trans k6).trans k7).mono
  have c7 := c3.of_keep kk5' (by decide) (by simp) K ws7
  have f32 : arr (ww (kK s0)) 32 ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_right _ _) (fit 32 (by decide))
  have G7 : num u7.mem (rvB s0) (ww (kK s0)) mG = j + 2 := by
    rw [kk5'.num (by decide) (by simp) (fit mG (by decide)), kk3.num (by decide) (by simp) (fit mG (by decide))]
    exact g2
  have Y7 : num u7.mem (rvB s0) (ww (kK s0)) mY = RR s0 % nV s0 := by
    rw [kk5'.num (by decide) (by simp) (fit mY (by decide)), v3]; exact c2.vO
  have Rc7 : num u7.mem (rvB s0) (wW (kK s0)) wRc = rR s0 := by
    rw [m7, m6, v5]; have := c3.vR; rw [← m4] at this; exact this
  have R24 : u7.gpr .r24 = BitVec.ofNat 64 j := by
    rw [K.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide)]; exact h24
  have R27 : u7.gpr .r27 = BitVec.ofNat 64 (cB s0) := by rw [a27, ← k7.gpr _ (by decide)]; exact c7.r26
  -- `g R mod n`.
  have hn0 : 0 < nV s0 := by have := hn.big; omega
  refine WP.mono (mmul_ok c7.base c7.ws (o := iG) (a := iG) (b := iR2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c7.r12 c7.inv
    (by rw [c7.vMN]; exact (show lowV u7.mem s0 mR2 < nV s0 by rw [c7.vR2]; exact Nat.mod_lt _ hn0)))
    fun t ⟨_, ws8, kk8, lt8, eq8, k8⟩ => ?_
  have c8 := c7.of_keep kk8 (by decide) (by simp) k8 ws8
  change num t.mem (rvB s0) (ww (kK s0)) mG < lowV u7.mem s0 mBase at lt8
  change num t.mem (rvB s0) (ww (kK s0)) mG * RR s0 % lowV u7.mem s0 mBase =
    lowV u7.mem s0 mG * lowV u7.mem s0 mR2 % lowV u7.mem s0 mBase at eq8
  rw [c7.vMN, c7.vR2, low_of_lt (by rw [G7]; have := hn.big; omega), G7, Nat.mul_mod_mod, ← Nat.mul_assoc] at eq8
  rw [c7.vMN] at lt8
  have G8 := VG.Proof.Bignum.mont_cancel hn.coprime eq8
  rw [Nat.mod_eq_of_lt lt8] at G8
  refine ⟨⟨c8, by rw [k8.gpr _ (by decide)]; exact R24, ?_, ?_, ?_⟩, by rw [k8.gpr _ (by decide)]; exact R27⟩
  · rw [kk8.num (by decide) (by simp) (fit mY (by decide)), Y7, Nat.pow_zero, Nat.mod_one, Nat.pow_zero,
      Nat.one_mul]
  · rw [G8, Nat.pow_zero, Nat.pow_one]
  · rw [keepW_num kk8 (j := wRc) (by decide) f32, Rc7, Nat.pow_zero, Nat.div_one]

end VG.Proof.Rsa.PPC64LE.Recover
