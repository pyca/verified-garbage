module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it
public import VerifiedGarbage.Proof.Rsa.Arm.RdDivB
public import VerifiedGarbage.Proof.Bignum.ShiftStages

import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.RdTaint
import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.RecoverDetWords

/-! # `vg_rsa_recover_primes_det` on ARMv7: the halvings by shifts

The `32 w` halvings (`TwoF`) leave `u` shifted right by its trailing zeros `t_u` (`tzc`, `32 w`
for zero; `ShiftStages.tz` capped at `32 w`, `tzc_min`), and `x` and `2^k x` shifted by
`k = min(t_u, t_x)` (`twos_iter`, from the shared `RecoverDetWords.twos_at`). `ctz_vp` counts the
trailing zeros a bit at a time; the shifts are masked stages of `2^i` bits, then of `2^i` words.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr aW)
open VG.Proof.Rsa (sub32 b2n)

/-! ## Trailing zeros -/

/-- The trailing zeros of `x` below bit `p` (`p` if `x` is zero there). -/
def tzc (x : Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => if x % 2 ^ (p + 1) = 0 then p + 1 else tzc x p

theorem tzc_le (x : Nat) : ∀ p, tzc x p ≤ p
  | 0 => Nat.le_refl _
  | p + 1 => by
    simp only [tzc]; split
    · exact Nat.le_refl _
    · have := tzc_le x p; omega_using [this]

theorem tzc_zero {x p : Nat} (h : x % 2 ^ p = 0) : tzc x p = p := by
  cases p with
  | zero => rfl
  | succ p => simp only [tzc, h, ↓reduceIte]

open VG.Proof.Bignum.ShiftStages (tz dvd_iff dvd_gcd_iff) in
/-- For `x ≠ 0`, the trailing zeros below bit `p` are `tz x` capped at `p`. -/
theorem tzc_min {x : Nat} (h0 : x ≠ 0) : ∀ p, tzc x p = min p (tz x)
  | 0 => by simp [tzc]
  | p + 1 => by
    simp only [tzc]
    have e : x % 2 ^ (p + 1) = 0 ↔ p + 1 ≤ tz x := by rw [← Nat.dvd_iff_mod_eq_zero, dvd_iff h0]
    by_cases c : p + 1 ≤ tz x
    · simp only [e.mpr c, ↓reduceIte]; omega_using [c]
    · simp only [show ¬ x % 2 ^ (p + 1) = 0 from fun h => c (e.mp h), ↓reduceIte, tzc_min h0 p]; omega_using [c]

open VG.Proof.Bignum.ShiftStages (tz dvd_iff dvd_gcd_iff) in
/-- Two numbers' common trailing zeros. -/
theorem tz_gcd {u x : Nat} (hu : u ≠ 0) (hx : x ≠ 0) : tz (Nat.gcd u x) = min (tz u) (tz x) := by
  have hg : Nat.gcd u x ≠ 0 := Nat.gcd_ne_zero_left hu
  have key : ∀ s, s ≤ tz (Nat.gcd u x) ↔ s ≤ tz u ∧ s ≤ tz x := fun s => by
    rw [← dvd_iff hg, ← dvd_gcd_iff, dvd_iff hu, dvd_iff hx]
  have h1 := (key (tz (Nat.gcd u x))).mp (Nat.le_refl _)
  have h2 := (key (min (tz u) (tz x))).mpr ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩
  omega_using [h1, h2]

/-- `N` halvings: shifts by the trailing zeros (`RecoverDetWords.twos_at`). -/
theorem twos_iter {f : Nat × Nat × Nat → Nat × Nat × Nat} {b : Nat}
    (hf : ∀ u x y, f (u, x, y) = if u % 2 = 0 then
      (if x % 2 = 0 then (u / 2, x / 2, 2 * y % 2 ^ b) else (u / 2, x, y)) else (u, x, y))
    (N u x X : Nat) (hu : u ≠ 0) (hX : X < 2 ^ b) :
    f^[N] (u, x, X) = (u / 2 ^ tzc u N, x / 2 ^ min (tzc u N) (tzc x N),
      X * 2 ^ min (tzc u N) (tzc x N) % 2 ^ b) := by
  have ef : f = VG.Proof.Rsa.RecoverDet.twoStep b := funext fun ⟨u, x, y⟩ => by
    rw [hf]; rfl
  have mt : min (tzc u N) (tzc x N) = min N (VG.Proof.Bignum.ShiftStages.tz (Nat.gcd u x)) := by
    rw [tzc_min hu]
    by_cases hx : x = 0
    · subst hx; rw [tzc_zero (by simp), Nat.gcd_zero_right]; omega_using []
    · rw [tzc_min hx, tz_gcd hu hx]; omega_using []
  rw [ef, VG.Proof.Rsa.RecoverDet.twos_at (by omega_using [hu]) hX N, mt, tzc_min hu]

/-! ## Counted loops and counts -/

/-- A loop of `K ≥ 1` iterations on `Z`. -/
theorem wp_count {body : Prog isa} {K : Nat} {I : Nat → State → Prop} (pos : 0 < K)
    (hb : ∀ k, k < K → ∀ s, I k s → WP isa body s fun t => I (k + 1) t ∧ t.z = decide (K - (k + 1) = 0))
    {s : State} (h : I 0 s) : WP isa (.loop body .ne) s (I K) := by
  refine WP.loop (M := isa) (fun n s => n < K ∧ I (K - 1 - n) s) (fun n s ⟨hn, hs⟩ => ?_) (K - 1) s
    ⟨by omega_using [pos], by rwa [show K - 1 - (K - 1) = 0 by omega_using []]⟩
  refine WP.mono (hb (K - 1 - n) (by omega_using [pos]) s hs) fun t ⟨ht, z⟩ => ?_
  by_cases h0 : n = 0
  · subst h0
    refine .inl ⟨?_, by rwa [show K - 1 - 0 + 1 = K by omega_using [pos]] at ht⟩
    show some (!t.z) = some false
    rw [z, show K - (K - 1 - 0 + 1) = 0 by omega_using []]; rfl
  · refine .inr ⟨?_, n - 1, by omega_using [h0], by omega_using [hn], by rwa [show K - 1 - (n - 1) = K - 1 - n + 1 by omega_using [hn, h0]]⟩
    show some (!t.z) = some true
    rw [z, decide_eq_false (show ¬ (K - (K - 1 - n + 1) = 0) by omega_using [hn, h0])]; rfl

theorem cnt_sub {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 32) :
    BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) ∧ (BitVec.ofNat 32 (n - 1) == 0) = decide (n - 1 = 0) := by
  refine ⟨?_, ?_⟩
  · rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [h1])]
  · by_cases e : n - 1 = 0
    · rw [e]; rfl
    · have : BitVec.ofNat 32 (n - 1) ≠ 0 := fun h0 => by
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h2])] at this
        exact e this
      rw [beq_eq_false_iff_ne.mpr this]; exact (decide_eq_false e).symm

theorem bit_or : ∀ a < 2, ∀ b < 2,
    BitVec.ofNat 32 a ||| BitVec.ofNat 32 b = BitVec.ofNat 32 (if a = 0 ∧ b = 0 then 0 else 1) := by decide
theorem bit_eor : ∀ a < 2, BitVec.ofNat 32 a ^^^ 1 = BitVec.ofNat 32 (1 - a) := by decide

/-! ## The trailing zeros -/

section
variable {P : RP}

/-- Bit `k` of word `i` of `x`: `r6` the bits left of the word, `r4` the trailing zeros below and `r5`
whether a bit below is set. -/
abbrev CB (P : RP) (j : Nat) (x : Nat) (i k : Nat) (s : State) : Prop :=
  s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.w j + 4 * (i + 1)) ∧ s.gpr .lr = BitVec.ofNat 32 (P.w - i) ∧
    s.gpr .r12 = BitVec.ofNat 32 (32 - k) ∧ s.gpr .r6 = BitVec.ofNat 32 (x / 2 ^ (32 * i + k) % 2 ^ (32 - k)) ∧
    s.gpr .r4 = BitVec.ofNat 32 (tzc x (32 * i + k)) ∧
    s.gpr .r5 = BitVec.ofNat 32 (if x % 2 ^ (32 * i + k) = 0 then 0 else 1)

theorem ctzBit_ok {j x i k : Nat} {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat} (hk : k < 32)
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.w nArr) (c : CB P j x i k s) :
    WP isa (.block ctzBit) s fun t => (KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.w nArr ∧ CB P j x i (k + 1) t) ∧
      t.z = decide (32 - (k + 1) = 0) := by
  obtain ⟨p0, plr, p12, p6, p4, p5⟩ := c
  unfold ctzBit
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r5]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r4]) (by simp)) u4.mem
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r6]) (by simp)) u5.mem
  refine wp_subs (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  obtain ⟨ht, hvt⟩ := h5.reg hv5 (ut.rest (ws := [.r12]) (by simp)) ut.mem
  set p := 32 * i + k with hp
  have ms : x % 2 ^ (p + 1) = x % 2 ^ p + 2 ^ p * (x / 2 ^ p % 2) := Nat.mod_pow_succ
  have pp := Nat.two_pow_pos p
  have bl : x / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
  have r1v : s1.gpr .r1 = BitVec.ofNat 32 (x / 2 ^ p % 2) := by
    rw [u1.gpr, dpVal, p6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 32 by decide),
      Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ (32 - k) from Nat.dvd_of_mod_eq_zero (by
        rw [show 32 - k = (31 - k) + 1 by omega_using [hk], Nat.pow_succ, Nat.mul_mod_left]))]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le bl (by decide))).symm
  have c5 : (if x % 2 ^ (p + 1) = 0 then 0 else 1) = (if (if x % 2 ^ p = 0 then 0 else 1) = 0 ∧
      x / 2 ^ p % 2 = 0 then 0 else 1) := by
    by_cases a : x % 2 ^ p = 0
    · by_cases b : x / 2 ^ p % 2 = 0
      · have : x % 2 ^ (p + 1) = 0 := by rw [ms, a, b]; rfl
        simp only [this, a, b, ↓reduceIte, and_self]
      · have : x % 2 ^ (p + 1) ≠ 0 := by rw [ms, a, show x / 2 ^ p % 2 = 1 by omega_using [b]]; omega_using [ms]
        simp only [this, a, b, ↓reduceIte, and_false]
    · have : x % 2 ^ (p + 1) ≠ 0 := by rw [ms]; omega_using [a]
      simp only [this, a, ↓reduceIte, Nat.one_ne_zero, false_and]
  have r5v : s2.gpr .r5 = BitVec.ofNat 32 (if x % 2 ^ (p + 1) = 0 then 0 else 1) := by
    rw [u2.gpr, dpVal, u1.other .r5 (by decide), p5, r1v, bit_or _ (by split <;> omega_using []) _ bl, c5]
  have r1v' : s3.gpr .r1 = BitVec.ofNat 32 (1 - if x % 2 ^ (p + 1) = 0 then 0 else 1) := by
    rw [u3.gpr, dpVal, r5v, bit_eor _ (by split <;> omega_using [])]
  refine ⟨⟨ht, hvt, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p0]
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), plr]
  · rw [ut.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p12, (cnt_sub (by omega_using [hk]) (by omega_using [])).1]; congr 1
  · rw [ut.other _ (by decide), u5.gpr, u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one,
      Nat.mod_eq_of_lt (a := x / 2 ^ p % 2 ^ (32 - k)) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) (by omega_using []))),
      show 32 - k = (32 - (k + 1)) + 1 by omega_using [hk], Nat.pow_succ, Nat.mul_comm _ 2, Nat.mod_mul_right_div_self,
      Nat.div_div_eq_div_mul, ← Nat.pow_succ, show 32 * i + (k + 1) = p + 1 by omega_using []]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by omega_using [])))).symm
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), p4, r1v', ← BitVec.ofNat_add,
      show 32 * i + (k + 1) = p + 1 by omega_using []]
    congr 1
    simp only [tzc]
    by_cases a : x % 2 ^ (p + 1) = 0
    · have a' : x % 2 ^ p = 0 := by omega_using [ms, a]
      simp only [a, ↓reduceIte, tzc_zero a', Nat.sub_zero]
    · simp only [a, ↓reduceIte, Nat.sub_self, Nat.add_zero]
  · rw [ut.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), r5v,
      show 32 * i + (k + 1) = p + 1 by omega_using []]
  · rw [zt, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), p12, (cnt_sub (by omega_using [hk]) (by omega_using [])).1, (cnt_sub (by omega_using [hk]) (by omega_using [])).2]
    congr 1

end


section
variable {P : RP}

/-- Before word `i` of the trailing zeros of `x`. -/
abbrev CO (P : RP) (j x i : Nat) (s : State) : Prop :=
  s.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.w j + 4 * i) ∧ s.gpr .lr = BitVec.ofNat 32 (P.w - i) ∧
    s.gpr .r4 = BitVec.ofNat 32 (tzc x (32 * i)) ∧
    s.gpr .r5 = BitVec.ofNat 32 (if x % 2 ^ (32 * i) = 0 then 0 else 1)

theorem ctzWord_ok {j i : Nat} {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat} (hj : j ∈ L)
    (hi : i < P.w) (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.w nArr) (c : CO P j (A j) i s) :
    WP isa ctzWord s fun t => (KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.w nArr ∧ CO P j (A j) (i + 1) t) ∧
      t.z = decide (P.w - (i + 1) = 0) := by
  obtain ⟨p0, plr, p4, p5⟩ := c
  have sz := h.sizes
  have wl := sz.wle
  have fj := fit_w sz (h.live_lt j hj)
  have fjZ := fitZ_w sz (h.live_lt j hj)
  simp only [S] at fj fjZ
  have dig : (s.mem.readW (off (State.addr P.B) (arr P.w j + 4 * i)) 32).toNat = A j / 2 ^ (32 * i) % 2 ^ 32 := by
    show w32 s.mem (State.addr P.B) (arr P.w j + 4 * i) = _
    have := h.arrs j hj
    simp only [num] at this
    rw [w32_digit _ _ _ hi, this]
  simp only [ctzWord, seqs]
  refine WP.seq ?_
  refine wp_ldr (by decide) (by rw [p0, BitVec.add_zero]; exact hv.addr (by omega_using [hi, fjZ])) (hv.read (by omega_using [hi, fjZ])) fun s1 u1 => ?_
  obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r6]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r0]) (by simp)) u2.mem
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r12]) (by simp)) u3.mem
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (wp_count (K := 32) (I := fun k t => KS P σ A L AW LW V LS t ∧ Ws t P.B P.Z P.w nArr ∧
    CB P j (A j) i k t) (by decide) (fun k hk t ⟨ht, hvt, ct⟩ => ctzBit_ok hk ht hvt ct) ⟨h3, hv3, ?_, ?_, ?_, ?_, ?_, ?_⟩) ?_)
  · rw [u3.other _ (by decide), u2.gpr, dpVal, u1.other _ (by decide), p0,
      show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.Rsa.Arm.KeyDiv.add_ofNat_assoc]
    congr 2
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), plr]
  · rw [u3.gpr]; rfl
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, Nat.add_zero, Nat.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [dig, BitVec.toNat_ofNat, Nat.mod_mod]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), p4, Nat.add_zero]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), p5, Nat.add_zero]
  intro t ⟨ht, hvt, q0, qlr, _, _, q4, q5⟩
  refine wp_subs (op2_imm (by decide)) fun t' ut zt => WP.block_nil ?_
  obtain ⟨ht', hvt'⟩ := ht.reg hvt (ut.rest (ws := [.lr]) (by simp)) ut.mem
  refine ⟨⟨ht', hvt', ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [ut.other _ (by decide), q0]
  · rw [ut.gpr, qlr, (cnt_sub (by omega_using [hi]) (by omega_using [wl])).1]; congr 1
  · rw [ut.other _ (by decide), q4, show 32 * i + 32 = 32 * (i + 1) by omega_using []]
  · rw [ut.other _ (by decide), q5, show 32 * i + 32 = 32 * (i + 1) by omega_using []]
  · rw [zt, qlr, (cnt_sub (by omega_using [hi]) (by omega_using [wl])).1, (cnt_sub (by omega_using [hi]) (by omega_using [wl])).2]; congr 1

/-- `ctz j d`: the trailing zeros of `[j]` below bit `32 w` at the slot `d`. -/
theorem ctz_vp {j d : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat} (hj : j ∈ L)
    (hj256 : j < 256) (hd : SlotOk d) (cert : DCert (ctz j d)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (ctz j d)
      (Dk P E A L AW LW (fun σ => upd (V σ) d (tzc (A σ j) (32 * P.w))) (d :: LS) P.w nArr) := by
  refine VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_
  have sz := h.sizes
  have wl := sz.wle
  have pos : 0 < P.w := by simp only [RP.w]; omega_using []
  simp only [ctz, seqs]
  refine WP.seq ?_
  refine ptr_ok hv (r := .r0) (by decide) (j := j) hj256 fun s1 p1 r1 m1 hv1 => ?_
  have h1 := h.of_rest r1 m1 (by decide)
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.lr]) (by simp)) u2.mem
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r4]) (by simp)) u3.mem
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r5]) (by simp)) u4.mem
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (wp_count (K := P.w) (I := fun i t => KS P σ (A σ) L (AW σ) LW (V σ) LS t ∧
    Ws t P.B P.Z P.w nArr ∧ CO P j (A σ j) i t) pos (fun i hi t ⟨ht, hvt, ct⟩ => ctzWord_ok hj hi ht hvt ct)
    ⟨h4, hv4, ?_, ?_, ?_, ?_⟩) ?_)
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), p1, Nat.mul_zero, Nat.add_zero]
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, hv1.r9, Nat.sub_zero]
  · rw [u4.other _ (by decide), u3.gpr]; rfl
  · rw [u4.gpr, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl
  intro t ⟨ht, hvt, _, _, q4, _⟩
  refine ht.strSlot hvt (d := d) (r := .r4) hd fun u hu hvu _ _ => WP.block_nil ⟨e, ?_, hvu⟩
  rw [q4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := tzc_le (A σ j) (32 * P.w); omega_using [wl, this])] at hu
  exact hu

end


section
variable {P : RP}

/-! ## Repeated halvings and doublings -/

theorem cntNext_ok {k n : Nat} (hk : k < n) (hn : n < 2 ^ 32) {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat}
    {v N : Nat} (h : KS P σ A L AW LW (upd V sK (n - k)) (sK :: LS) s) (hv : Ws s P.B P.Z v N) :
    WP isa (.block cntNext) s fun t =>
      (KS P σ A L AW LW (upd V sK (n - (k + 1))) (sK :: LS) t ∧ Ws t P.B P.Z v N) ∧
        t.z = decide (n - (k + 1) = 0) := by
  unfold cntNext
  refine h.ldrSlot hv (d := sK) (by simp) (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := sK) (r := .r1) (by decide) fun t ht hvt _ zt => WP.block_nil ⟨⟨?_, hvt⟩, ?_⟩
  · have e : (s2.gpr .r1).toNat = n - (k + 1) := by
      rw [u2.gpr, u1.gpr, upd_self, (cnt_sub (by omega_using [hk]) (by omega_using [hn])).1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
      omega_using []
    rw [e] at ht
    refine ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨?_, ?_⟩)
    · simp only [List.mem_cons] at hd ⊢; grind
    · simp only [upd]; split <;> rfl
  · rw [zt, z2, u1.gpr, upd_self, (cnt_sub (by omega_using [hk]) (by omega_using [hn])).1, (cnt_sub (by omega_using [hk]) (by omega_using [hn])).2]
    congr 1

/-- `halfK j k`: `[j] := ⌊[j] / 2^k⌋`, the slot `sK` cleared. -/
theorem halfK_vp {j k : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hk : 0 < k ∧ k < 32) (hj : j ∈ L) (hlW : ∀ i ∈ LW, j / 2 ≠ i) (cert : DCert (halfK j k)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (halfK j k)
      (Dk P E (fun σ => upd (A σ) j (A σ j / 2 ^ k)) L AW LW (fun σ => upd (V σ) sK 0) (sK :: LS) P.w nArr) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    rw [halfK, WP.seq_iff]
    refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
    obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r11]) (by simp)) u1.mem
    have z1 : (s1.gpr .r11).toNat = 0 := by rw [u1.gpr]; rfl
    refine h1.strSlot hv1 (d := sK) (r := .r11) (by decide) fun s2 h2 hv2 g2 _ => WP.block_nil ?_
    rw [z1] at h2
    refine WP.mono (h2.halfK_w hk hv2 hj (by rw [g2]; exact z1) hlW) fun t ⟨ht, hvt, _⟩ =>
      ⟨e, ht.mono (fun i hi => ⟨List.mem_cons_of_mem _ hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), hvt⟩

/-- `shlK j k`: `[j] := [j] 2^k` modulo `2^(32 W)`, wide, the slot `sK` cleared. -/
theorem shlK_vp {j k : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hk : 0 < k ∧ k < 32) (hj : j ∈ LW) (hl : ∀ i ∈ L, i / 2 ≠ j) (cert : DCert (shlK j k)) :
    VP (Dk P E A L AW LW V LS P.W 22) (shlK j k)
      (Dk P E A L (fun σ => upd (AW σ) j (AW σ j * 2 ^ k % 2 ^ (32 * P.W))) LW (fun σ => upd (V σ) sK 0) (sK :: LS)
        P.W 22) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => by
    rw [shlK, WP.seq_iff]
    refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
    obtain ⟨h1, hv1⟩ := h.reg hv (u1.rest (ws := [.r11]) (by simp)) u1.mem
    have z1 : (s1.gpr .r11).toNat = 0 := by rw [u1.gpr]; rfl
    refine h1.strSlot hv1 (d := sK) (r := .r11) (by decide) fun s2 h2 hv2 g2 _ => WP.block_nil ?_
    rw [z1] at h2
    refine WP.mono (h2.shlK_W hk hv2 hj (by rw [g2]; exact z1) hl) fun t ⟨ht, hvt, _⟩ =>
      ⟨e, ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨List.mem_cons_of_mem _ hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), hvt⟩

end


/-! ## The bit stages -/

theorem shift_sel_div (v t i : Nat) :
    (if t / 2 ^ i % 2 = 0 then v / 2 ^ (t % 2 ^ i) else v / 2 ^ (t % 2 ^ i) / 2 ^ (2 ^ i)) =
      v / 2 ^ (t % 2 ^ (i + 1)) := by
  rw [VG.Proof.Bignum.ShiftStages.mod_two_pow_succ]
  split
  · rename_i b; rw [b, Nat.zero_mul, Nat.add_zero]
  · rename_i b; rw [show t / 2 ^ i % 2 = 1 by omega_using [b], Nat.one_mul, VG.Proof.Bignum.ShiftStages.div_pow_add]

theorem shift_sel_mul (X t i M : Nat) :
    (if t / 2 ^ i % 2 = 0 then X * 2 ^ (t % 2 ^ i) % 2 ^ M else X * 2 ^ (t % 2 ^ i) % 2 ^ M * 2 ^ (2 ^ i) % 2 ^ M) =
      X * 2 ^ (t % 2 ^ (i + 1)) % 2 ^ M := by
  rw [VG.Proof.Bignum.ShiftStages.mod_two_pow_succ]
  split
  · rename_i b; rw [b, Nat.zero_mul, Nat.add_zero]
  · rename_i b
    rw [show t / 2 ^ i % 2 = 1 by omega_using [b], Nat.one_mul, VG.Proof.Bignum.ShiftStages.mul_pow_add_mod]

section
variable {P : RP}

theorem copyN_vp {o a : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < nArr) (ha : a ∈ L) (hoa : o ≠ a) (hlW : ∀ j ∈ LW, o / 2 ≠ j) (cert : DCert (copy o a)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (copy o a)
      (Dk P E (fun σ => upd (A σ) o (A σ a)) (o :: L) AW LW V LS P.w nArr) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ =>
    WP.mono (h.copy_w hv ho ha hoa hlW) fun _ ⟨ht, hvt, _⟩ => ⟨e, ht, hvt⟩

theorem selN_vp {o a b sl : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < nArr) (ha : a ∈ L) (hb : b ∈ L) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS)
    (bit : ∀ σ, E σ → V σ sl ≤ 1) (hlW : ∀ j ∈ LW, o / 2 ≠ j) (cert : DCert (sel o a b sl)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (sel o a b sl)
      (Dk P E (fun σ => upd (A σ) o (if V σ sl = 0 then A σ a else A σ b)) (o :: L) AW LW V LS P.w nArr) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ =>
    WP.mono (h.sel_w hv ho ha hb hoa hob hsl (bit _ e) hlW) fun _ ⟨ht, hvt, _⟩ => ⟨e, ht, hvt⟩

theorem selW_vp {o a b sl : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (ho : o < 22) (ha : a ∈ LW) (hb : b ∈ LW) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS)
    (bit : ∀ σ, E σ → V σ sl ≤ 1) (hl : ∀ j ∈ L, j / 2 ≠ o) (cert : DCert (sel o a b sl)) :
    VP (Dk P E A L AW LW V LS P.W 22) (sel o a b sl)
      (Dk P E A L (fun σ => upd (AW σ) o (if V σ sl = 0 then AW σ a else AW σ b)) (o :: LW) V LS P.W 22) :=
  VP.dctx cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hv⟩ =>
    WP.mono (h.sel_W hv ho ha hb hoa hob hsl (bit _ e) hl) fun _ ⟨ht, hvt, _⟩ => ⟨e, ht, hvt⟩

theorem bitTo_ok {src i : Nat} (hi : i < 32) {σ s : State} {A AW V : Nat → Nat} {L LW LS : List Nat} {v N : Nat}
    (hs : src ∈ LS) (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z v N) :
    WP isa (.block (bitTo src i)) s fun t =>
      KS P σ A L AW LW (upd V sBit (V src / 2 ^ i % 2)) (sBit :: LS) t ∧ Ws t P.B P.Z v N := by
  have vl : V src < 2 ^ 32 := by rw [← h.sl src hs]; exact BitVec.isLt _
  unfold bitTo
  refine h.ldrSlot hv (d := src) hs (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  have r1v : (s1.gpr .r1).toNat = V src := by rw [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt vl]
  have fin : ∀ s2 : State, (s2.gpr .r1).toNat = V src / 2 ^ i → KS P σ A L AW LW V LS s2 → Ws s2 P.B P.Z v N →
      WP isa (.block [.dp .and .r1 .r1 (.imm 1), .str .r1 .r8 sBit]) s2 fun t =>
        KS P σ A L AW LW (upd V sBit (V src / 2 ^ i % 2)) (sBit :: LS) t ∧ Ws t P.B P.Z v N := by
    intro s2 e2 h2 hv2
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
    obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
    refine h3.strSlot hv3 (d := sBit) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨?_, hvt⟩
    rwa [u3.gpr, dpVal, BitVec.toNat_and, e2, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod] at ht
  cases i with
  | zero =>
    simp only [↓reduceIte]
    exact fin s1 (by rw [r1v, Nat.pow_zero, Nat.div_one]) h1 hv1
  | succ i =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    refine wp_mov (op2_lsr (by omega_using [hi])) fun s2 u2 => ?_
    obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
    exact fin s2 (by rw [u2.gpr, BitVec.toNat_ushiftRight, r1v, Nat.shiftRight_eq_div_pow]) h2 hv2

end



section
variable {P : RP}

/-- A narrow array's half of a bit stage: `[a]` shifted right by `2^i` bits where bit `i` of `t` is set. -/
theorem nStage_vp {a src i : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    {v t : State → Nat} {H : State → State → Prop} {rest : Prog isa}
    (hi : i < 5) (ha : a ∈ L) (ha22 : a < nArr) (haT : a ≠ aT1 ∧ a ≠ aT2) (hLT : ∀ j ∈ L, j ≠ aT1 ∧ j ≠ aT2)
    (hsrc : src ∈ LS) (hLW : ∀ j ∈ LW, aT1 / 2 ≠ j ∧ a / 2 ≠ j)
    (vA : ∀ σ, E σ → A σ a = v σ / 2 ^ (t σ % 2 ^ i)) (vS : ∀ σ, E σ → V σ src = t σ)
    (cBit : DCert (.block (bitTo src i))) (cC1 : DCert (copy aT1 a)) (cS : DCert (sel aT2 a aT1 sBit))
    (cC2 : DCert (copy a aT2))
    (hrest : VP (Dk P E (fun σ => upd (A σ) a (v σ / 2 ^ (t σ % 2 ^ (i + 1)))) L AW LW
      (fun σ => upd (upd (V σ) sBit (t σ / 2 ^ i % 2)) sK 0) (sK :: sBit :: LS) P.w nArr) rest H) :
    VP (Dk P E A L AW LW V LS P.w nArr)
      (.seq (.block (bitTo src i)) (.seq (copy aT1 a) (.seq (halfK aT1 (2 ^ i))
        (.seq (sel aT2 a aT1 sBit) (.seq (copy a aT2) rest))))) H := by
  have p : 2 ^ i < 32 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (show i ≤ 4 by omega_using [hi])) (by decide)
  refine VP.seq (G := Dk P E A L AW LW (fun σ => upd (V σ) sBit (t σ / 2 ^ i % 2)) (sBit :: LS) P.w nArr)
    (VP.dctx cBit (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (bitTo_ok (by omega_using [hi]) hsrc h hv) fun y ⟨hy, hvy⟩ => ⟨e, by rwa [vS σ e] at hy, hvy⟩) ?_
  refine (copyN_vp (o := aT1) (a := a) (by decide) ha (Ne.symm haT.1) (fun j hj => (hLW j hj).1) cC1).seq ?_
  refine (halfK_vp (j := aT1) (k := 2 ^ i) ⟨Nat.two_pow_pos _, p⟩ (List.mem_cons_self ..)
    (fun j hj => (hLW j hj).1) (halfKT1_taint i hi)).seq ?_
  refine (selN_vp (o := aT2) (a := a) (b := aT1) (sl := sBit) (by decide) (List.mem_cons_of_mem _ ha)
    (List.mem_cons_self ..) (Ne.symm haT.2) (by decide) (by simp)
    (fun σ _ => by simp only [upd_ne _ _ (show sBit ≠ sK by decide), upd_self]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    (fun j hj => by rw [show aT2 / 2 = aT1 / 2 by decide]; exact (hLW j hj).1) cS).seq ?_
  refine VP.seq ((copyN_vp (o := a) (a := aT2) ha22 (List.mem_cons_self ..) haT.2 (fun j hj => (hLW j hj).2)
    cC2).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)), ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩) hrest
  obtain ⟨j1, j2⟩ := hLT j hj
  by_cases c : j = a
  · subst c
    simp only [upd_self, upd_ne _ _ haT.1, upd_ne _ _ (show sBit ≠ sK by decide)]
    rw [vA σ e]; exact shift_sel_div _ _ _
  · simp only [upd_ne _ _ c, upd_ne _ _ j1, upd_ne _ _ j2]

/-- The wide part of a bit stage: `[wX3]` shifted left by `2^i` bits where bit `i` of `t` (at `sBit`) is set. -/
theorem wPart_vp {i : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    {X t : State → Nat} (hi : i < 5) (hW : wX3 ∈ LW) (hLWT : ∀ j ∈ LW, j ≠ wT1 ∧ j ≠ wT2)
    (hL : ∀ j ∈ L, j / 2 ≠ wT1 ∧ j / 2 ≠ wT2 ∧ j / 2 ≠ wX3) (hB : sBit ∈ LS)
    (vW : ∀ σ, E σ → AW σ wX3 = X σ * 2 ^ (t σ % 2 ^ i) % 2 ^ (32 * P.W))
    (vB : ∀ σ, E σ → V σ sBit = t σ / 2 ^ i % 2) :
    VP (Dk P E A L AW LW V LS P.w nArr)
      (seqs [.block toW, copy wT1 wX3, shlK wT1 (2 ^ i), sel wT2 wX3 wT1 sBit, copy wX3 wT2, .block toN])
      (Dk P E A L (fun σ => upd (AW σ) wX3 (X σ * 2 ^ (t σ % 2 ^ (i + 1)) % 2 ^ (32 * P.W))) LW
        (fun σ => upd (V σ) sK 0) (sK :: LS) P.w nArr) := by
  have p : 2 ^ i < 32 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (show i ≤ 4 by omega_using [hi])) (by decide)
  simp only [seqs]
  refine toW_vp.seq ((copyW_vp (o := wT1) (a := wX3) (by decide) hW (by decide) (fun j hj => (hL j hj).1)
    copyWT1_taint).seq ((shlK_vp (j := wT1) (k := 2 ^ i) ⟨Nat.two_pow_pos _, p⟩
    (List.mem_cons_self ..) (fun j hj => (hL j hj).1) (shlKT1_taint i hi)).seq
    ((selW_vp (o := wT2) (a := wX3) (b := wT1) (sl := sBit) (by decide) (List.mem_cons_of_mem _ hW)
      (List.mem_cons_self ..) (by decide) (by decide) (List.mem_cons_of_mem _ hB)
      (fun σ e => by simp only [upd_ne _ _ (show sBit ≠ sK by decide)]; rw [vB σ e]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
      (fun j hj => (hL j hj).2.1) selW_taint).seq ?_)))
  refine VP.seq ((copyW_vp (o := wX3) (a := wT2) (by decide) (List.mem_cons_self ..) (by decide)
    (fun j hj => (hL j hj).2.2) copyWT2_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono
      (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)), ?_⟩)
      (fun d hd => ⟨hd, rfl⟩), hv⟩) toN_vp
  obtain ⟨j1, j2⟩ := hLWT j hj
  by_cases c : j = wX3
  · subst c
    simp only [upd_self, upd_ne _ _ (show wX3 ≠ wT1 by decide), upd_ne _ _ (show sBit ≠ sK by decide)]
    rw [vB σ e, vW σ e]; exact shift_sel_mul _ _ _ _
  · simp only [upd_ne _ _ c, upd_ne _ _ j1, upd_ne _ _ j2]

end


section
variable {P : RP}

/-- Bit stage `i`: `u` shifted right by `2^i` bits where bit `i` of `t_u` is set, `x` right and `X` left
where bit `i` of `k` is. -/
theorem bitStage_vp {i : Nat} (hi : i < 5) {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    {u x X tu k : State → Nat} (hU : aU ∈ L) (hX : aX2 ∈ L) (hW : wX3 ∈ LW)
    (hLT : ∀ j ∈ L, j ≠ aT1 ∧ j ≠ aT2) (hL : ∀ j ∈ L, j / 2 ≠ wT1 ∧ j / 2 ≠ wT2 ∧ j / 2 ≠ wX3)
    (hLW : ∀ j ∈ LW, j ≠ 18 ∧ j ≠ 4 ∧ j ≠ 10 ∧ j ≠ wT1 ∧ j ≠ wT2)
    (hS : sTu ∈ LS ∧ sKv ∈ LS) (hSB : ∀ d ∈ LS, d ≠ sBit)
    (vU : ∀ σ, E σ → A σ aU = u σ / 2 ^ (tu σ % 2 ^ i)) (vX : ∀ σ, E σ → A σ aX2 = x σ / 2 ^ (k σ % 2 ^ i))
    (vW : ∀ σ, E σ → AW σ wX3 = X σ * 2 ^ (k σ % 2 ^ i) % 2 ^ (32 * P.W))
    (vT : ∀ σ, E σ → V σ sTu = tu σ) (vK : ∀ σ, E σ → V σ sKv = k σ) :
    VP (Dk P E A L AW LW V LS P.w nArr) (bitStage i)
      (Dk P E (fun σ => upd (upd (A σ) aU (u σ / 2 ^ (tu σ % 2 ^ (i + 1)))) aX2 (x σ / 2 ^ (k σ % 2 ^ (i + 1)))) L
        (fun σ => upd (AW σ) wX3 (X σ * 2 ^ (k σ % 2 ^ (i + 1)) % 2 ^ (32 * P.W))) LW
        (fun σ => upd (V σ) sK 0) (sK :: LS) P.w nArr) := by
  have hKB : sKv ≠ sBit ∧ sKv ≠ sK := by decide
  simp only [bitStage, seqs]
  refine nStage_vp (a := aU) (src := sTu) (v := u) (t := tu) hi hU (by decide) (by decide) hLT hS.1
    (fun j hj => by
      have := hLW j hj
      rw [show aT1 / 2 = 18 by decide, show aU / 2 = 4 by decide]
      exact ⟨fun e => this.1 e.symm, fun e => this.2.1 e.symm⟩) vU vT (bitToU_taint i hi) copyT1U_taint
    selU_taint copyUT2_taint ?_
  refine nStage_vp (a := aX2) (src := sKv) (v := x) (t := k) hi hX (by decide) (by decide) hLT
    (by simp [hS.2]) (fun j hj => by
      have := hLW j hj
      rw [show aT1 / 2 = 18 by decide, show aX2 / 2 = 10 by decide]
      exact ⟨fun e => this.1 e.symm, fun e => this.2.2.1 e.symm⟩)
    (fun σ e => by rw [upd_ne _ _ (show aX2 ≠ aU by decide)]; exact vX σ e)
    (fun σ e => by simp only [upd_ne _ _ hKB.1, upd_ne _ _ hKB.2]; exact vK σ e)
    (bitToK_taint i hi) copyT1X_taint selX_taint copyXT2_taint ?_
  refine (wPart_vp (X := X) (t := k) hi hW (fun j hj => by have := hLW j hj; exact ⟨this.2.2.2.1, this.2.2.2.2⟩) hL
    (by simp) vW (fun σ _ => by simp only [upd_ne _ _ (show sBit ≠ sK by decide), upd_self])).mono
    (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨?_, ?_⟩), hv⟩
  · simp only [List.mem_cons] at hd ⊢; grind
  · by_cases c : d = sK
    · subst c; simp only [upd_self]
    · simp only [List.mem_cons] at hd
      rcases hd with c' | hd
      · exact absurd c' c
      · simp only [upd_ne _ _ c, upd_ne _ _ (hSB d hd)]

end


section
variable {P : RP}

/-- `shrW o a`: `[o] := ⌊[a] / 2^(32 sh)⌋`, narrow, for `4 sh` at `sWs`. -/
theorem shrW_vp {o a sh : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    (hsh : sh < P.w) (ho : o < nArr) (ha : a ∈ L) (hoa : o ≠ a) (hz : aZN ∈ L) (hoz : o ≠ aZN)
    (hLW : ∀ j ∈ LW, o / 2 ≠ j) (hS : sWs ∈ LS) (z0 : ∀ σ, E σ → A σ aZN = 0) (vS : ∀ σ, E σ → V σ sWs = 4 * sh)
    (certC : DCert (copy o aZN)) (certA : DCert (.block (ptr .r10 a ++ ([.ldr .r1 .r8 sWs] : List Instr))))
    (certB : ShiftCert .r10 (shiftDownB o)) :
    VP (Dk P E A L AW LW V LS P.w nArr) (shrW o a)
      (Dk P E (fun σ => upd (A σ) o (A σ a / 2 ^ (32 * sh))) (o :: L) AW LW V LS P.w nArr) := by
  simp only [shrW, shiftDownBy, seqs]
  refine VP.seq (G := Dk P E (fun σ => upd (A σ) o 0) (o :: L) AW LW V LS P.w nArr)
    (VP.dctx certC (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_) ?_
  · refine WP.mono (h.copy_w hv (o := o) (a := aZN) ho hz hoz hLW) fun t ⟨ht, hvt, _⟩ => ⟨e, ?_, hvt⟩
    rwa [z0 σ e] at ht
  refine VP.seq (G := fun σ t => Dk P E (fun σ => upd (A σ) o 0) (o :: L) AW LW V LS P.w nArr σ t ∧
      t.gpr .r10 = P.B + BitVec.ofNat 32 (arr P.w a) ∧ t.gpr .r1 = BitVec.ofNat 32 (4 * sh))
    (VP.dctx certA (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ => ?_)
    (VP.taint _ certB (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨e, h, hv⟩, p10, p1⟩ => ?_)
  · have ha22 := h.live_lt a (List.mem_cons_of_mem _ ha)
    refine ptr_ok hv (r := .r10) (by decide) (j := a) (by have : nArr ≤ 256 := (by decide); omega_using [ha22, this])
      fun s1 p1 r1 m1 hv1 => ?_
    have h1 := h.of_rest r1 m1 (by decide)
    refine h1.ldrSlot hv1 (d := sWs) hS (r := .r1) (by decide) fun t ht hvt U => WP.block_nil ⟨⟨e, ht, hvt⟩, ?_, ?_⟩
    · rw [U.other _ (by decide), p1]
    · rw [U.gpr, vS σ e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.1.2.2.r7, h₂.1.2.2.r7]
    · rw [h₁.1.2.2.r8, h₂.1.2.2.r8]
    · rw [h₁.1.2.2.r9, h₂.1.2.2.r9]
  · have sz := h.sizes
    have wl := sz.wle
    have ha22 := h.live_lt a (List.mem_cons_of_mem _ ha)
    refine WP.mono (shiftDownB_ok hv ho ha22 (by decide) hoa hsh p10 p1) fun t ⟨hvt, O, V', R⟩ =>
      ⟨e, ?_, hvt⟩
    have fo := fit_w sz ho
    have fa := fit_w sz ha22
    simp only [S] at fo fa
    have k : Keep P.B P.w [o] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O) (by simp only [S]; omega_using [])
      (by simp)
    have v0 := h.arrs o (List.mem_cons_self ..)
    simp only [upd_self] at v0
    rw [numW_at _ _ _ _ (P.w - sh) (by omega_using [])] at v0
    have h0 : val32 s.mem (State.addr P.B) (arr P.w o + 4 * (P.w - sh)) (P.w - (P.w - sh)) = 0 := by
      have := Nat.two_pow_pos (32 * (P.w - sh))
      rcases Nat.eq_zero_or_pos (val32 s.mem (State.addr P.B) (arr P.w o + 4 * (P.w - sh)) (P.w - (P.w - sh)))
        with c | c
      · exact c
      · have := Nat.mul_pos this c; omega_using [v0, this]
    have va := h.arrs a (List.mem_cons_of_mem _ ha)
    simp only [upd_ne _ _ (Ne.symm hoa)] at va
    rw [numW_at _ _ _ _ sh (by omega_using [hsh])] at va
    have ev' : num t.mem P.B P.w o = A σ a / 2 ^ (32 * sh) := by
      rw [numW_at _ _ _ _ (P.w - sh) (by omega_using []),
        O.val32 (d := arr P.w o + 4 * (P.w - sh)) (k := P.w - (P.w - sh)) (Or.inr (by omega_using [])) (by omega_using [fo]), h0,
        V', ← va,
        Nat.mul_zero, Nat.add_zero, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.zero_add]
    have h' := h.write_w k ho (by simp) (h.r8_of R) R.sp R.rd R.wr ev' hLW (by simp)
    refine h'.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
    · simp only [List.mem_cons] at hj
      simp only [upd]; split <;> rfl

theorem kMin_ok {tu kx : Nat} (htu : tu < 2 ^ 31) (hkx : kx < 2 ^ 31) {σ s : State} {A AW V : Nat → Nat}
    {L LW LS : List Nat} {v N : Nat} (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z v N)
    (hT : sTu ∈ LS) (hK : sKx ∈ LS) (vT : V sTu = tu) (vK : V sKx = kx) :
    WP isa (.block kMin) s fun t => KS P σ A L AW LW (upd (upd (upd (upd V sKv (min tu kx)) sKk (min tu kx / 32))
      sTk (tu / 32)) sWs 4) (sWs :: sTk :: sKk :: sKv :: LS) t ∧ Ws t P.B P.Z v N := by
  unfold kMin
  refine h.ldrSlot hv (d := sTu) hT (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine h1.ldrSlot hv1 (d := sKx) hK (r := .r2) (by decide) fun s2 h2 hv2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨h3, hv3⟩ := h2.reg hv2 (u3.rest (ws := [.r3]) (by simp)) u3.mem
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  obtain ⟨h4, hv4⟩ := h3.reg hv3 (u4.rest (ws := [.r4]) (by simp)) u4.mem
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r5]) (by simp)) u5.mem
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  obtain ⟨h6, hv6⟩ := h5.reg hv5 (u6.rest (ws := [.r4]) (by simp)) u6.mem
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  obtain ⟨h7, hv7⟩ := h6.reg hv6 (u7.rest (ws := [.r3]) (by simp)) u7.mem
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r1]) (by simp)) u8.mem
  have a1 : s7.gpr .r1 = BitVec.ofNat 32 tu := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr, vT]
  have a3 : s3.gpr .r3 = BitVec.ofNat 32 kx - BitVec.ofNat 32 tu := by
    rw [u3.gpr, dpVal, u2.gpr, u2.other .r1 (by decide), u1.gpr, vT, vK]
  have a4 : s6.gpr .r4 = 0 - (if kx < tu then 1 else 0) := by
    rw [u6.gpr, dpVal, u5.gpr, u5.other .r4 (by decide), u4.gpr, a3, sign_bit hkx htu]
  have a6 : s6.gpr .r3 = BitVec.ofNat 32 kx - BitVec.ofNat 32 tu := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), a3]
  have m8 : s8.gpr .r1 = BitVec.ofNat 32 (min tu kx) := by
    rw [u8.gpr, dpVal, u7.gpr, dpVal, a1, a6, a4]
    by_cases c : kx < tu
    · simp only [c, ↓reduceIte, Nat.min_def, show ¬ tu ≤ kx by omega_using [c]]
      rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes, BitVec.add_comm, BitVec.sub_add_cancel]
    · simp only [c, ↓reduceIte, Nat.min_def, show tu ≤ kx by omega_using [c]]
      rw [show (0 : BitVec 32) - 0 = 0 by decide,
        show ∀ y : BitVec 32, y &&& 0 = 0 from fun y => BitVec.and_zero,
        show ∀ y : BitVec 32, y + 0 = y from fun y => BitVec.add_zero y]
  have mt : min tu kx < 2 ^ 31 := by omega_using [htu]
  refine h8.strSlot hv8 (d := sKv) (r := .r1) (by decide) fun s9 h9 hv9 g9 _ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
  obtain ⟨h10, hv10⟩ := h9.reg hv9 (u10.rest (ws := [.r1]) (by simp)) u10.mem
  refine h10.strSlot hv10 (d := sKk) (r := .r1) (by decide) fun s11 h11 hv11 g11 _ => ?_
  refine h11.ldrSlot hv11 (d := sTu) (by simp [hT]) (r := .r1) (by decide) fun s12 h12 hv12 u12 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s13 u13 => ?_
  obtain ⟨h13, hv13⟩ := h12.reg hv12 (u13.rest (ws := [.r1]) (by simp)) u13.mem
  refine h13.strSlot hv13 (d := sTk) (r := .r1) (by decide) fun s14 h14 hv14 g14 _ => ?_
  refine wp_mov (op2_imm (by decide)) fun s15 u15 => ?_
  obtain ⟨h15, hv15⟩ := h14.reg hv14 (u15.rest (ws := [.r1]) (by simp)) u15.mem
  refine h15.strSlot hv15 (d := sWs) (r := .r1) (by decide) fun t ht hvt _ _ => WP.block_nil ⟨?_, hvt⟩
  have e9 : (s8.gpr .r1).toNat = min tu kx := by rw [m8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [htu])]
  have e10 : (s10.gpr .r1).toNat = min tu kx / 32 := by
    rw [u10.gpr, BitVec.toNat_ushiftRight, g9, e9, Nat.shiftRight_eq_div_pow]
  have e13 : (s13.gpr .r1).toNat = tu / 32 := by
    rw [u13.gpr, BitVec.toNat_ushiftRight, u12.gpr, Nat.shiftRight_eq_div_pow]
    simp only [upd_ne _ _ (show sTu ≠ sKk by decide), upd_ne _ _ (show sTu ≠ sKv by decide), vT,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show tu < 2 ^ 32 by omega_using [htu])]
  rw [u15.gpr, e13, e10, e9] at ht
  exact ht

end


/-! ## The word stages -/

theorem shift_sel_divW (v c q m : Nat) :
    (if q / 2 ^ m % 2 = 0 then v / 2 ^ (c + 32 * (q % 2 ^ m))
      else v / 2 ^ (c + 32 * (q % 2 ^ m)) / 2 ^ (32 * 2 ^ m)) = v / 2 ^ (c + 32 * (q % 2 ^ (m + 1))) := by
  rw [VG.Proof.Bignum.ShiftStages.mod_two_pow_succ]
  split
  · rename_i b; rw [b, Nat.zero_mul, Nat.add_zero]
  · rename_i b
    rw [show q / 2 ^ m % 2 = 1 by omega_using [b], Nat.one_mul, VG.Proof.Bignum.ShiftStages.div_pow_add]
    congr 2; rw [Nat.mul_add]; omega_using []

theorem mulW (X e sh W : Nat) (h : sh ≤ W) :
    X * 2 ^ e % 2 ^ (32 * W) % 2 ^ (32 * (W - sh)) * 2 ^ (32 * sh) = X * 2 ^ (e + 32 * sh) % 2 ^ (32 * W) := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using [])), ← Nat.mul_mod_mul_right, ← Nat.pow_add,
    show 32 * (W - sh) + 32 * sh = 32 * W by omega_using [h], Nat.mul_assoc, ← Nat.pow_add]

theorem shift_sel_mulW (X c q m W : Nat) (h : 2 ^ m ≤ W) :
    (if q / 2 ^ m % 2 = 0 then X * 2 ^ (c + 32 * (q % 2 ^ m)) % 2 ^ (32 * W)
      else X * 2 ^ (c + 32 * (q % 2 ^ m)) % 2 ^ (32 * W) % 2 ^ (32 * (W - 2 ^ m)) * 2 ^ (32 * 2 ^ m)) =
      X * 2 ^ (c + 32 * (q % 2 ^ (m + 1))) % 2 ^ (32 * W) := by
  rw [VG.Proof.Bignum.ShiftStages.mod_two_pow_succ]
  split
  · rename_i b; rw [b, Nat.zero_mul, Nat.add_zero]
  · rename_i b
    rw [show q / 2 ^ m % 2 = 1 by omega_using [b], Nat.one_mul, mulW _ _ _ _ h]
    congr 3; rw [Nat.mul_add]; omega_using []

section
variable {P : RP}

/-- A narrow array's half of a word stage: `[a]` shifted right by `2^m` words where bit `m` of `q` is set. -/
theorem wnStage_vp {a src m : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    {v c q : State → Nat} {H : State → State → Prop} {rest : Prog isa}
    (hm : 2 ^ m < P.w) (ha : a ∈ L) (ha22 : a < nArr) (haT : a ≠ aT1 ∧ a ≠ aT2 ∧ a ≠ aZN)
    (hLT : ∀ j ∈ L, j ≠ aT1 ∧ j ≠ aT2) (hz : aZN ∈ L) (z0 : ∀ σ, E σ → A σ aZN = 0)
    (hsrc : src ∈ LS) (hWs : sWs ∈ LS) (hWB : sWs ≠ sBit) (hLW : ∀ j ∈ LW, aT1 / 2 ≠ j ∧ a / 2 ≠ j)
    (vA : ∀ σ, E σ → A σ a = v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ m))) (vS : ∀ σ, E σ → V σ src = q σ / 2 ^ m)
    (vW : ∀ σ, E σ → V σ sWs = 4 * 2 ^ m)
    (cBit : DCert (.block (bitTo src 0))) (cA : DCert (.block (ptr .r10 a ++ ([.ldr .r1 .r8 sWs] : List Instr))))
    (cS : DCert (sel aT2 a aT1 sBit)) (cC2 : DCert (copy a aT2))
    (hrest : VP (Dk P E (fun σ => upd (A σ) a (v σ / 2 ^ (c σ + 32 * (q σ % 2 ^ (m + 1))))) L AW LW
      (fun σ => upd (V σ) sBit (q σ / 2 ^ m % 2)) (sBit :: LS) P.w nArr) rest H) :
    VP (Dk P E A L AW LW V LS P.w nArr)
      (.seq (.block (bitTo src 0)) (.seq (shrW aT1 a) (.seq (sel aT2 a aT1 sBit) (.seq (copy a aT2) rest)))) H := by
  refine VP.seq (G := Dk P E A L AW LW (fun σ => upd (V σ) sBit (q σ / 2 ^ m % 2)) (sBit :: LS) P.w nArr)
    (VP.dctx cBit (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (bitTo_ok (i := 0) (by omega_using []) hsrc h hv) fun y ⟨hy, hvy⟩ =>
        ⟨e, by rwa [vS σ e, Nat.pow_zero, Nat.div_one] at hy, hvy⟩) ?_
  refine (shrW_vp (o := aT1) (a := a) (sh := 2 ^ m) hm (by decide) ha (Ne.symm haT.1) hz (by decide)
    (fun j hj => (hLW j hj).1) (List.mem_cons_of_mem _ hWs) z0
    (fun σ e => by rw [upd_ne _ _ hWB]; exact vW σ e) copyT1Z_taint cA downT1_taint).seq ?_
  refine (selN_vp (o := aT2) (a := a) (b := aT1) (sl := sBit) (by decide) (List.mem_cons_of_mem _ ha)
    (List.mem_cons_self ..) (Ne.symm haT.2.1) (by decide) (List.mem_cons_self ..)
    (fun σ _ => by simp only [upd_self]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    (fun j hj => by rw [show aT2 / 2 = aT1 / 2 by decide]; exact (hLW j hj).1) cS).seq ?_
  refine VP.seq ((copyN_vp (o := a) (a := aT2) ha22 (List.mem_cons_self ..) haT.2.1 (fun j hj => (hLW j hj).2)
    cC2).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)), ?_⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩) hrest
  obtain ⟨j1, j2⟩ := hLT j hj
  by_cases cj : j = a
  · subst cj
    simp only [upd_self, upd_ne _ _ haT.1]
    rw [vA σ e]; exact shift_sel_divW _ _ _ _
  · simp only [upd_ne _ _ cj, upd_ne _ _ j1, upd_ne _ _ j2]

/-- The wide part of a word stage: `[wX3]` shifted left by `2^m` words where bit `m` of `q` (at `sBit`) is set. -/
theorem wwPart_vp {m : Nat} {L LW LS : List Nat} {E : State → Prop} {A AW V : State → Nat → Nat}
    {X c q : State → Nat} {H : State → State → Prop} {rest : Prog isa}
    (hm : 2 ^ m < P.w) (hW : wX3 ∈ LW) (hz : wZ ∈ LW) (z0 : ∀ σ, E σ → AW σ wZ = 0)
    (hLWT : ∀ j ∈ LW, j ≠ wT1 ∧ j ≠ wT2)
    (hL : ∀ j ∈ L, j / 2 ≠ wT1 ∧ j / 2 ≠ wT2 ∧ j / 2 ≠ wX3) (hB : sBit ∈ LS) (hWs : sWs ∈ LS)
    (vX : ∀ σ, E σ → AW σ wX3 = X σ * 2 ^ (c σ + 32 * (q σ % 2 ^ m)) % 2 ^ (32 * P.W))
    (vB : ∀ σ, E σ → V σ sBit = q σ / 2 ^ m % 2) (vW : ∀ σ, E σ → V σ sWs = 4 * 2 ^ m)
    (hrest : VP (Dk P E A L (fun σ => upd (AW σ) wX3 (X σ * 2 ^ (c σ + 32 * (q σ % 2 ^ (m + 1))) % 2 ^ (32 * P.W)))
      LW V LS P.w nArr) rest H) :
    VP (Dk P E A L AW LW V LS P.w nArr)
      (.seq (.block toW) (.seq (shiftUpBy sWs wT1 wX3) (.seq (sel wT2 wX3 wT1 sBit) (.seq (copy wX3 wT2)
        (.seq (.block toN) rest))))) H := by
  have hW' : 2 ^ m < P.W := by simp only [RP.W]; omega_using [hm]
  refine toW_vp.seq ((shiftUpBy_vp (d := sWs) (sh := 2 ^ m) (o := wT1) (a := wX3) hW' (by decide) hW (by decide) hz
    (by decide) (fun j hj => (hL j hj).1) hWs z0 vW copyWT1Z_taint ptrWT1_taint upBX3_taint).seq
    ((selW_vp (o := wT2) (a := wX3) (b := wT1) (sl := sBit) (by decide) (List.mem_cons_of_mem _ hW)
      (List.mem_cons_self ..) (by decide) (by decide) hB
      (fun σ e => by rw [vB σ e]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
      (fun j hj => (hL j hj).2.1) selW_taint).seq ?_))
  refine VP.seq ((copyW_vp (o := wX3) (a := wT2) (by decide) (List.mem_cons_self ..) (by decide)
    (fun j hj => (hL j hj).2.2) copyWT2_taint).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono
      (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)), ?_⟩)
      (fun d hd => ⟨hd, rfl⟩), hv⟩) (toN_vp.seq hrest)
  obtain ⟨j1, j2⟩ := hLWT j hj
  by_cases cj : j = wX3
  · subst cj
    simp only [upd_self, upd_ne _ _ (show wX3 ≠ wT1 by decide)]
    rw [vB σ e, vX σ e]; exact shift_sel_mulW _ _ _ _ _ (by omega_using [hW'])
  · simp only [upd_ne _ _ cj, upd_ne _ _ j1, upd_ne _ _ j2]

end


/-- The word stages' count: `2^KW ≥ w`. -/
abbrev KW (P : RP) : Nat := Nat.log2 (P.w - 1) + 1

section
variable {P : RP}

theorem halfSlot {q m : Nat} {V : Nat → Nat} {d : Nat} (hv : V d = q / 2 ^ m) (hq : q / 2 ^ m < 2 ^ 32) :
    ((BitVec.ofNat 32 (V d)) >>> 1).toNat = q / 2 ^ (m + 1) := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hv, Nat.mod_eq_of_lt hq, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem wsEnd_ok {m q1 q2 : Nat} {LS : List Nat} {σ s : State} {A AW V : Nat → Nat} {L LW : List Nat}
    (hm : 2 ^ m < P.w) (hT : sTk ∈ LS) (hK : sKk ∈ LS) (hW : sWs ∈ LS)
    (vT : V sTk = q1 / 2 ^ m) (vK : V sKk = q2 / 2 ^ m) (vW : V sWs = 4 * 2 ^ m)
    (h : KS P σ A L AW LW V LS s) (hv : Ws s P.B P.Z P.w nArr) :
    WP isa (.block [.ldr .r1 .r8 sTk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sTk,
      .ldr .r1 .r8 sKk, .mov .r1 (.shifted .r1 .lsr 1), .str .r1 .r8 sKk,
      .ldr .r1 .r8 sWs, .mov .r1 (.shifted .r1 .lsl 1), .str .r1 .r8 sWs,
      .dp .sub .r1 .r1 (.shifted .r9 .lsl 2), .mov .r1 (.shifted .r1 .lsr 31), .cmp .r1 (.imm 0)]) s fun t =>
      (KS P σ A L AW LW (upd (upd (upd V sTk (q1 / 2 ^ (m + 1))) sKk (q2 / 2 ^ (m + 1))) sWs (4 * 2 ^ (m + 1)))
        (sWs :: sKk :: sTk :: LS) t ∧ Ws t P.B P.Z P.w nArr) ∧ t.z = decide (KW P - (m + 1) = 0) := by
  have sz := h.sizes
  have wl := sz.wle
  have w2 : 2 ≤ P.w := by simp only [RP.w]; omega_using []
  have p1 : 2 ^ (m + 1) ≤ 2 * P.w := by rw [Nat.pow_succ]; omega_using [hm]
  have b1 : q1 / 2 ^ m < 2 ^ 32 := by rw [← vT, ← h.sl sTk hT]; exact BitVec.isLt _
  have b2 : q2 / 2 ^ m < 2 ^ 32 := by rw [← vK, ← h.sl sKk hK]; exact BitVec.isLt _
  refine h.ldrSlot hv (d := sTk) hT (r := .r1) (by decide) fun s1 h1 hv1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hv2⟩ := h1.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2.strSlot hv2 (d := sTk) (r := .r1) (by decide) fun s3 h3 hv3 g3 _ => ?_
  refine h3.ldrSlot hv3 (d := sKk) (by simp [hK]) (r := .r1) (by decide) fun s4 h4 hv4 u4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hv5⟩ := h4.reg hv4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine h5.strSlot hv5 (d := sKk) (r := .r1) (by decide) fun s6 h6 hv6 g6 _ => ?_
  refine h6.ldrSlot hv6 (d := sWs) (by simp [hW]) (r := .r1) (by decide) fun s7 h7 hv7 u7 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s8 u8 => ?_
  obtain ⟨h8, hv8⟩ := h7.reg hv7 (u8.rest (ws := [.r1]) (by simp)) u8.mem
  refine h8.strSlot hv8 (d := sWs) (r := .r1) (by decide) fun s9 h9 hv9 g9 _ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s10 u10 => ?_
  obtain ⟨h10, hv10⟩ := h9.reg hv9 (u10.rest (ws := [.r1]) (by simp)) u10.mem
  refine wp_mov (op2_lsr (by decide)) fun s11 u11 => ?_
  obtain ⟨h11, hv11⟩ := h10.reg hv10 (u11.rest (ws := [.r1]) (by simp)) u11.mem
  refine wp_cmp (op2_imm (by decide)) fun t ut zt => WP.block_nil ?_
  obtain ⟨ht, hvt⟩ := h11.reg hv11 (ut.rest []) ut.mem
  have e2 : (s2.gpr .r1).toNat = q1 / 2 ^ (m + 1) := by rw [u2.gpr, u1.gpr]; exact halfSlot vT b1
  have e5 : (s5.gpr .r1).toNat = q2 / 2 ^ (m + 1) := by
    rw [u5.gpr, u4.gpr]; exact halfSlot (by rw [upd_ne _ _ (show sKk ≠ sTk by decide), vK]) b2
  have e8 : (s8.gpr .r1).toNat = 4 * 2 ^ (m + 1) := by
    rw [u8.gpr, u7.gpr]
    simp only [upd_ne _ _ (show sWs ≠ sKk by decide), upd_ne _ _ (show sWs ≠ sTk by decide), vW]
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_succ, Nat.pow_succ 2 m,
      Nat.mod_eq_of_lt (by omega_using [hm, wl]), Nat.mod_eq_of_lt (by omega_using [hm, wl])]; omega_using []
  have r11v : s11.gpr .r1 = if 4 * 2 ^ (m + 1) < 4 * P.w then 1 else 0 := by
    rw [u11.gpr, u10.gpr, dpVal, hv9.r9, g9]
    rw [show s8.gpr .r1 = BitVec.ofNat 32 (4 * 2 ^ (m + 1)) from BitVec.eq_of_toNat_eq (by
      rw [e8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [e8])])]
    rw [show BitVec.ofNat 32 P.w <<< 2 = BitVec.ofNat 32 (4 * P.w) from BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (a := P.w) (by omega_using [wl])]; omega_using [])]
    exact sign_bit (by omega_using [hm, wl]) (by omega_using [wl])
  refine ⟨⟨ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨?_, ?_⟩), hvt⟩, ?_⟩
  · simp only [List.mem_cons] at hd ⊢; grind
  · rw [e8, e5, e2]
  · rw [zt, r11v]
    have e : 4 * 2 ^ (m + 1) < 4 * P.w ↔ m + 1 ≤ Nat.log2 (P.w - 1) := by
      rw [Nat.le_log2 (by omega_using [w2])]; omega_using [hm]
    by_cases c : m + 1 ≤ Nat.log2 (P.w - 1)
    · simp only [e.mpr c, ↓reduceIte]
      have : ¬ KW P - (m + 1) = 0 := by simp only [KW]; omega_using [c]
      simp only [this, decide_false]; rfl
    · simp only [show ¬ 4 * 2 ^ (m + 1) < 4 * P.w from fun h => c (e.mp h), ↓reduceIte]
      have : KW P - (m + 1) = 0 := by simp only [KW]; omega_using [c]
      simp only [this, decide_true]; rfl

end


/-- After `m` word stages (and the bit stages). -/
def WAm (A0 : Nat → Nat) (u x tu k m : Nat) : Nat → Nat :=
  upd (upd A0 aU (u / 2 ^ (tu % 32 + 32 * (tu / 32 % 2 ^ m)))) aX2 (x / 2 ^ (k % 32 + 32 * (k / 32 % 2 ^ m)))
def WWm (P : RP) (AW0 : Nat → Nat) (X k m : Nat) : Nat → Nat :=
  upd AW0 wX3 (X * 2 ^ (k % 32 + 32 * (k / 32 % 2 ^ m)) % 2 ^ (32 * P.W))
def WVm (V0 : Nat → Nat) (tu k m : Nat) : Nat → Nat :=
  upd (upd (upd V0 sTk (tu / 32 / 2 ^ m)) sKk (k / 32 / 2 ^ m)) sWs (4 * 2 ^ m)
abbrev LSW (LS0 : List Nat) : List Nat := sWs :: sTk :: sKk :: LS0

section
variable {P : RP}

theorem kw_pow {m : Nat} (hm : m < KW P) : 2 ^ m < P.w := by
  have w2 : 2 ≤ P.w := by simp only [RP.w]; omega_using []
  have := Nat.log2_self_le (n := P.w - 1) (by omega_using [w2])
  have := Nat.pow_le_pow_right (n := 2) (by decide) (show m ≤ Nat.log2 (P.w - 1) by simp only [KW] at hm; omega_using [hm])
  omega_arith

theorem wordStage_vp {m : Nat} (hm : m < KW P) {L LW LS0 : List Nat} {E : State → Prop}
    {A0 AW0 V0 : State → Nat → Nat} {u x X tu k : State → Nat}
    (hU : aU ∈ L) (hX : aX2 ∈ L) (hz : aZN ∈ L) (hW : wX3 ∈ LW) (hzW : wZ ∈ LW)
    (z0 : ∀ σ, E σ → A0 σ aZN = 0) (zW : ∀ σ, E σ → AW0 σ wZ = 0)
    (hLT : ∀ j ∈ L, j ≠ aT1 ∧ j ≠ aT2) (hL : ∀ j ∈ L, j / 2 ≠ wT1 ∧ j / 2 ≠ wT2 ∧ j / 2 ≠ wX3)
    (hLW : ∀ j ∈ LW, j ≠ 18 ∧ j ≠ 4 ∧ j ≠ 10 ∧ j ≠ wT1 ∧ j ≠ wT2)
    (hLS : ∀ d ∈ LS0, d ≠ sBit ∧ d ≠ sTk ∧ d ≠ sKk ∧ d ≠ sWs) :
    VP (fun σ s => E σ ∧ (KS P σ (WAm (A0 σ) (u σ) (x σ) (tu σ) (k σ) m) L (WWm P (AW0 σ) (X σ) (k σ) m) LW
        (WVm (V0 σ) (tu σ) (k σ) m) (LSW LS0) s ∧ Ws s P.B P.Z P.w nArr))
      wordStage
      (fun σ s => (E σ ∧ (KS P σ (WAm (A0 σ) (u σ) (x σ) (tu σ) (k σ) (m + 1)) L (WWm P (AW0 σ) (X σ) (k σ) (m + 1))
        LW (WVm (V0 σ) (tu σ) (k σ) (m + 1)) (LSW LS0) s ∧ Ws s P.B P.Z P.w nArr)) ∧
        s.z = decide (KW P - (m + 1) = 0)) := by
  have hm' := kw_pow hm
  simp only [wordStage, seqs]
  refine wnStage_vp (a := aU) (src := sTk) (v := u) (c := fun σ => tu σ % 32) (q := fun σ => tu σ / 32) hm' hU
    (by decide) (by decide) hLT hz (fun σ e => by simp only [WAm]; rd_up; exact z0 σ e) (by simp) (by simp)
    (by decide) (fun j hj => by
      have := hLW j hj
      rw [show aT1 / 2 = 18 by decide, show aU / 2 = 4 by decide]
      exact ⟨fun e => this.1 e.symm, fun e => this.2.1 e.symm⟩)
    (fun σ _ => by simp only [WAm]; rd_up) (fun σ _ => by simp only [WVm]; rd_up)
    (fun σ _ => by simp only [WVm]; rd_up) stBit_taint ptrU_taint selU_taint copyUT2_taint ?_
  refine wnStage_vp (a := aX2) (src := sKk) (v := x) (c := fun σ => k σ % 32) (q := fun σ => k σ / 32) hm' hX
    (by decide) (by decide) hLT hz (fun σ e => by simp only [WAm]; rd_up; exact z0 σ e) (by simp) (by simp)
    (by decide) (fun j hj => by
      have := hLW j hj
      rw [show aT1 / 2 = 18 by decide, show aX2 / 2 = 10 by decide]
      exact ⟨fun e => this.1 e.symm, fun e => this.2.2.1 e.symm⟩)
    (fun σ _ => by simp only [WAm]; rd_up) (fun σ _ => by simp only [WVm]; rd_up)
    (fun σ _ => by simp only [WVm]; rd_up) stBitK_taint ptrX_taint selX_taint copyXT2_taint ?_
  refine wwPart_vp (X := X) (c := fun σ => k σ % 32) (q := fun σ => k σ / 32) hm' hW hzW
    (fun σ e => by simp only [WWm]; rd_up; exact zW σ e)
    (fun j hj => by have := hLW j hj; exact ⟨this.2.2.2.1, this.2.2.2.2⟩) hL (by simp) (by simp)
    (fun σ _ => by simp only [WWm]; rd_up) (fun σ _ => by rd_up) (fun σ _ => by simp only [WVm]; rd_up) ?_
  refine VP.dctx wsEnd_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
    WP.mono (wsEnd_ok (q1 := tu σ / 32) (q2 := k σ / 32) hm' (by simp) (by simp) (by simp)
      (by simp only [WVm]; rd_up) (by simp only [WVm]; rd_up) (by simp only [WVm]; rd_up) h hv)
      fun t ⟨⟨ht, hvt⟩, z⟩ => ⟨⟨e, ht.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨?_, ?_⟩), hvt⟩, z⟩
  · simp only [WAm]
    by_cases c1 : j = aX2
    · subst c1; simp only [upd_self]
    · by_cases c2 : j = aU
      · subst c2; simp only [upd_self, upd_ne _ _ c1]
      · simp only [upd_ne _ _ c1, upd_ne _ _ c2]
  · simp only [WWm]
    by_cases c1 : j = wX3
    · subst c1; simp only [upd_self]
    · simp only [upd_ne _ _ c1]
  · simp only [LSW, List.mem_cons] at hd ⊢; grind
  · simp only [WVm]
    simp only [LSW, List.mem_cons] at hd
    rcases hd with rfl | rfl | rfl | hd
    · rd_up
    · rd_up
    · rd_up
    · obtain ⟨a1, a2, a3, a4⟩ := hLS d hd
      simp only [upd_ne _ _ a1, upd_ne _ _ a2, upd_ne _ _ a3, upd_ne _ _ a4]

end


section
variable {P : RP}

theorem twosInit_ok {f : Nat × Nat × Nat → Nat × Nat × Nat} {σ s : State}
    (h : KS P σ (AN P) [aN] (AW1 P σ) [wX, wOne, wZ] (V1 P σ) [sOkDE] s) (hw : Ws s P.B P.Z P.W 22) :
    WP isa twosInit s fun t => KS P σ (AT P f σ 0) LT (AWT P f σ 0) LWT (V1 P σ) [sOkDE] t ∧
      Ws t P.B P.Z P.w nArr := by
  simp only [twosInit, seqs]
  refine WP.seq (WP.mono (h.copy_W hw (o := wX3) (a := wX) (by decide) (by decide) (by decide)
    (by decide)) fun s1 ⟨h1, hw1, _⟩ => ?_)
  refine WP.seq (h1.toN hw1 fun s2 h2 hw2 _ => WP.block_nil ?_)
  have h2' := h2.narrow (j := wX) (by decide) (by decide)
  rw [show 2 * wX = aX2 from rfl] at h2'
  have h3 := h2'.mono (A' := upd (AN P) aX2 (xV P σ % 2 ^ (32 * P.w))) (live' := [aX2, aN])
    (AW' := upd (AW1 P σ) wX3 (xV P σ)) (liveW' := [wX3, wOne, wZ]) (V' := V1 P σ) (ls' := [sOkDE])
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AN, AW1] <;> rd_ev)
    (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> exact ⟨by decide, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h3.sub_w hw2 (o := aZN) (a := aN) (b := aN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s4 ⟨h4, hw4, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h4.copy_w hw4 (o := aOneN) (a := aZN) (by decide) (by decide) (by decide)
    (by decide)) fun s5 ⟨h5, hw5, _, _⟩ => ?_)
  refine WP.seq (h5.setOne_w hw5 (j := aOneN) (by decide) (by decide) fun s6 h6 hw6 _ => WP.block_nil ?_)
  refine WP.mono (h6.sub_w hw6 (o := aU) (a := aN) (b := aOneN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t ⟨ht, hwt, _, _⟩ => ⟨?_, hwt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp only [AT, AN, ts, Function.iterate_zero, id] <;> rd_ev
  · simp only [LWT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp only [AWT, AW1, ts, Function.iterate_zero, id] <;> rd_ev
  · exact ⟨hd, rfl⟩

end


/-! ## The halvings -/

/-- `u`, `x mod 2^(32 w)` and `x` after `twosInit`, the trailing zeros of `u`, and `k`. -/
abbrev tU0 (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := AT P f σ 0 aU
abbrev tX0 (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := AT P f σ 0 aX2
abbrev tW0 (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := AWT P f σ 0 wX3
abbrev tTu (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := tzc (tU0 P f σ) (32 * P.w)
abbrev tKx (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := tzc (tX0 P f σ) (32 * P.w)
abbrev tKv (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) : Nat := min (tTu P f σ) (tKx P f σ)

/-- After `i` bit stages. -/
def BA (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (i : Nat) (σ : State) : Nat → Nat :=
  upd (upd (AT P f σ 0) aU (tU0 P f σ / 2 ^ (tTu P f σ % 2 ^ i))) aX2 (tX0 P f σ / 2 ^ (tKv P f σ % 2 ^ i))
def BW (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (i : Nat) (σ : State) : Nat → Nat :=
  upd (AWT P f σ 0) wX3 (tW0 P f σ * 2 ^ (tKv P f σ % 2 ^ i) % 2 ^ (32 * P.W))

section
variable {P : RP}

theorem bitStageB_vp {f : Nat × Nat × Nat → Nat × Nat × Nat} {i : Nat} (hi : i < 5) {E : State → Prop}
    {V : State → Nat → Nat} {LS : List Nat} (hS : sTu ∈ LS ∧ sKv ∈ LS) (hSB : ∀ d ∈ LS, d ≠ sBit)
    (vT : ∀ σ, E σ → V σ sTu = tTu P f σ) (vK : ∀ σ, E σ → V σ sKv = tKv P f σ) :
    VP (Dk P E (BA P f i) LT (BW P f i) LWT V LS P.w nArr) (bitStage i)
      (Dk P E (BA P f (i + 1)) LT (BW P f (i + 1)) LWT (fun σ => upd (V σ) sK 0) (sK :: LS) P.w nArr) := by
  refine (bitStage_vp hi (u := tU0 P f) (x := tX0 P f) (X := tW0 P f) (tu := tTu P f) (k := tKv P f)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hS hSB
    (fun σ _ => by simp only [BA]; rd_up) (fun σ _ => by simp only [BA]; rd_up)
    (fun σ _ => by simp only [BW]; rd_up) vT vK).mono (fun _ _ h => h) fun σ s ⟨e, h, hv⟩ =>
      ⟨e, h.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩), hv⟩
  · simp only [BA]
    by_cases c1 : j = aX2
    · subst c1; simp only [upd_self]
    · by_cases c2 : j = aU
      · subst c2; simp only [upd_self, upd_ne _ _ c1]
      · simp only [upd_ne _ _ c1, upd_ne _ _ c2]
  · simp only [BW]
    by_cases c1 : j = wX3
    · subst c1; simp only [upd_self]
    · simp only [upd_ne _ _ c1]

end


theorem tzc_lt {x : Nat} : ∀ {p}, x % 2 ^ p ≠ 0 → tzc x p < p
  | 0, h => by rw [Nat.pow_zero, Nat.mod_one] at h; exact absurd rfl h
  | p + 1, h => by
    simp only [tzc, h, ↓reduceIte]; have := tzc_le x p; omega_using [this]

/-- The stages' shift of `t < 32 w` bits. -/
theorem stage_shift {t w K : Nat} (ht : t < 32 * w) (hK : w - 1 < 2 ^ K) : t % 32 + 32 * (t / 32 % 2 ^ K) = t := by
  rw [Nat.mod_eq_of_lt (a := t / 32) (by omega_using [ht, hK])]; omega_using []

section
variable {P : RP}

/-- `twos`: the `32 w` halvings, by the trailing zeros and shifts. -/
theorem twosW_vp {f : Nat × Nat × Nat → Nat × Nat × Nat} (hf : TwoF P f) {E : State → Prop} (hn2 : 2 ≤ P.n) :
    VP (Dk P E (fun _ => AN P) [aN] (AW1 P) [wX, wOne, wZ] (V1 P) [sOkDE] P.W 22) twos
      (fun σ s => E σ ∧ TI P f σ (32 * P.w) s) := by
  simp only [twos, seqs]
  refine VP.seq (G := Dk P E (fun σ => AT P f σ 0) LT (fun σ => AWT P f σ 0) LWT (V1 P) [sOkDE] P.w nArr)
    (VP.dctx twosInit_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (twosInit_ok h hv) fun t ⟨ht, hvt⟩ => ⟨e, ht, hvt⟩) ?_
  refine VP.of_imp (p := P.n < 2 ^ (32 * P.w) ∧ P.w ≤ 258) (fun σ s ⟨_, h, _⟩ => ⟨by
    have := h.lt_w (j := aN) (by decide)
    change AT P f σ 0 aN < 2 ^ (32 * P.w) at this
    rwa [show AT P f σ 0 aN = P.n by simp only [AT]; rd_ev] at this, h.sizes.wle⟩) fun ⟨hnw, wl⟩ => ?_
  have w2 : 2 ≤ P.w := by simp only [RP.w]; omega_using []
  have u0v : ∀ σ, tU0 P f σ = P.n - 1 := fun σ => by
    simp only [tU0, AT, ts, Function.iterate_zero, id]; rd_ev
    unfold sub32; rw [show P.n + 2 ^ (32 * P.w) - 1 = (P.n - 1) + 2 ^ (32 * P.w) by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
  have u1 : sub32 P.w P.n 1 ≠ 0 := by
    unfold sub32; rw [show P.n + 2 ^ (32 * P.w) - 1 = (P.n - 1) + 2 ^ (32 * P.w) by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]; omega_using [hn2]
  have tuL : ∀ σ, tTu P f σ < 32 * P.w := fun σ =>
    tzc_lt (by rw [u0v, Nat.mod_eq_of_lt (by omega_arith)]; omega_using [hn2])
  have tuB : ∀ σ, tTu P f σ < 2 ^ 31 := fun σ => by have := tuL σ; omega_arith
  have kxB : ∀ σ, tKx P f σ < 2 ^ 31 := fun σ => by have := tzc_le (tX0 P f σ) (32 * P.w); simp only [tKx]; omega_arith
  refine (ctz_vp (j := aU) (d := sTu) (by decide) (by decide) (by decide) ctzU_taint).seq
    ((ctz_vp (j := aX2) (d := sKx) (by decide) (by decide) (by decide) ctzX_taint).seq ?_)
  refine VP.seq (G := Dk P E (BA P f 0) LT (BW P f 0) LWT (fun σ => upd (upd (upd (upd (upd (upd (V1 P σ) sTu
      (tTu P f σ)) sKx (tKx P f σ)) sKv (tKv P f σ)) sKk (tKv P f σ / 32)) sTk (tTu P f σ / 32)) sWs 4)
      [sWs, sTk, sKk, sKv, sKx, sTu, sOkDE] P.w nArr)
    (VP.dctx kMin_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hv⟩ =>
      WP.mono (kMin_ok (tu := tTu P f σ) (kx := tKx P f σ) (tuB σ) (kxB σ) h hv (by simp) (by simp)
        (by rd_up) (by rd_up)) fun t ⟨ht, hvt⟩ => ⟨e, ht.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩)
          (fun d hd => ⟨hd, rfl⟩), hvt⟩) ?_
  · simp only [BA, Nat.pow_zero, Nat.mod_one, Nat.div_one]
    simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> rd_up
  · have := ht.lt_W (j := wX3) (by decide)
    simp only [BW, Nat.pow_zero, Nat.mod_one, Nat.mul_one]
    simp only [LWT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · rw [upd_self]; exact (Nat.mod_eq_of_lt this).symm
    · rd_up
    · rd_up
  refine (bitStageB_vp (i := 0) (by decide) (by simp) (by decide) (fun σ _ => by rd_up) (fun σ _ => by rd_up)).seq
    ((bitStageB_vp (i := 1) (by decide) (by simp) (by decide) (fun σ _ => by rd_up) (fun σ _ => by rd_up)).seq
    ((bitStageB_vp (i := 2) (by decide) (by simp) (by decide) (fun σ _ => by rd_up) (fun σ _ => by rd_up)).seq
    ((bitStageB_vp (i := 3) (by decide) (by simp) (by decide) (fun σ _ => by rd_up) (fun σ _ => by rd_up)).seq
    ((bitStageB_vp (i := 4) (by decide) (by simp) (by decide) (fun σ _ => by rd_up) (fun σ _ => by rd_up)).seq ?_))))
  have pos : 0 < KW P := by simp only [KW]; omega_using []
  let I := fun m σ s => KS P σ (WAm (AT P f σ 0) (tU0 P f σ) (tX0 P f σ) (tTu P f σ) (tKv P f σ) m) LT
    (WWm P (AWT P f σ 0) (tW0 P f σ) (tKv P f σ) m) LWT
    (WVm (upd (upd (upd (upd (V1 P σ) sTu (tTu P f σ)) sKx (tKx P f σ)) sKv (tKv P f σ)) sK 0)
      (tTu P f σ) (tKv P f σ) m) (LSW [sK, sKv, sKx, sTu, sOkDE]) s ∧ Ws s P.B P.Z P.w nArr
  refine VP.mono (F := fun σ s => E σ ∧ I 0 σ s) (VP.count (E := E) (I := I) pos fun m hm => wordStage_vp hm
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun σ _ => by simp only [AT]; rd_ev)
    (fun σ _ => by simp only [AWT]; rd_ev) (by decide) (by decide) (by decide) (by decide))
    (fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨?_, ?_⟩), hv⟩)
    (fun σ s ⟨e, h, hv⟩ => ⟨e, h.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨?_, ?_⟩), hv⟩)
  · simp only [WAm, BA, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero, Nat.reduceAdd, Nat.reducePow]
  · simp only [WWm, BW, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.add_zero, Nat.reduceAdd, Nat.reducePow]
  · simp only [LSW, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [WVm, Nat.pow_zero, Nat.div_one, Nat.mul_one]
    simp only [LSW, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rd_up
  · have tl := tuL σ
    have hK : P.w - 1 < 2 ^ KW P := Nat.lt_log2_self
    have it := twos_iter hf (32 * P.w) (sub32 P.w P.n 1) (xV P σ % 2 ^ (32 * P.w)) _ u1 (show xV P σ < 2 ^ (32 * P.W) from Nat.mod_lt _ (Nat.two_pow_pos _))
    simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · simp only [WAm, AT, ts]; rd_ev
      rw [it, stage_shift tl hK]; simp only [tTu, tU0, AT, ts, Function.iterate_zero, id]; rd_ev
    · simp only [WAm, AT, ts]; rd_ev
      rw [it, stage_shift (show tKv P f σ < 32 * P.w by simp only [tKv]; omega_using [tl]) hK]
      simp only [tKv, tTu, tKx, tU0, tX0, AT, ts, Function.iterate_zero, id]; rd_ev
    all_goals (simp only [WAm, AT]; rd_ev)
  · have hK : P.w - 1 < 2 ^ KW P := Nat.lt_log2_self
    have it := twos_iter hf (32 * P.w) (sub32 P.w P.n 1) (xV P σ % 2 ^ (32 * P.w)) _ u1 (show xV P σ < 2 ^ (32 * P.W) from Nat.mod_lt _ (Nat.two_pow_pos _))
    simp only [LWT, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [WWm, AWT, ts]; rd_ev
      rw [it, stage_shift (show tKv P f σ < 32 * P.w by have := tuL σ; simp only [tKv]; omega_using [this]) hK]
      simp only [tKv, tTu, tKx, tU0, tX0, tW0, AT, AWT, ts, Function.iterate_zero, id]; rd_ev
    all_goals (simp only [WWm, AWT]; rd_ev)
  · simp only [LST, LSW, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with rfl | rfl <;> simp
  · simp only [LST, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp only [VT, WVm, V1, Nat.sub_self] <;> rd_up

end

end VG.Proof.Rsa.Arm.RecoverDet
