import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Ctx
import VerifiedGarbage.Proof.RsaKeyGen.KeyOp

/-!
# An RSA key from its primes on x86-64: the results, against `keyOp`

What the zeros (`outsRes_zeros`) and `keyPart` (`outsRes_tail`) leave is
`keyOp`'s status and outputs.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)
open VG.Spec.RsaKeyGen (keyOp keyStatus keyFromPrimes)

/-- The status and the outputs `keyOp` gives. -/
def OutsRes (I : KIn) (m : Mem) (rax : BitVec 64) : Prop :=
  (rax.setWidth 32).toNat = keyStatus (keyOp I.pl I.eb I.pb I.qb) ∧
    match keyOp I.pl I.eb I.pb I.qb with
    | .inl (.ok ys) => (outsL I).map (fun o => bytesAt m o.1 o.2) = ys
    | _ => ∀ o ∈ outsL I, bytesAt m o.1 o.2 = List.replicate o.2 0

theorem keyOp_inr {pl : Nat} {eB pB qB : List Byte}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) = .inr ()) :
    keyOp pl eB pB qB = .inr () := by
  unfold keyOp; rw [h]

theorem keyOp_error {pl : Nat} {eB pB qB : List Byte} {f : Spec.RsaKeyGen.Failure}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.error f)) :
    keyOp pl eB pB qB = .inl (.error f) := by
  unfold keyOp; rw [h]

theorem keyOp_ok {pl : Nat} {eB pB qB : List Byte} {k : Spec.RsaKeyGen.Key}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.ok k)) :
    keyOp pl eB pB qB = .inl (.ok [Spec.Rsa.i2osp k.n (2 * pl), Spec.Rsa.i2osp k.d (2 * pl),
      Spec.Rsa.i2osp k.p pl, Spec.Rsa.i2osp k.q pl, Spec.Rsa.i2osp k.dP pl,
      Spec.Rsa.i2osp k.dQ pl, Spec.Rsa.i2osp k.qInv pl]) := by
  unfold keyOp; rw [h]

theorem setWidth32 (n : Nat) (h : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h]

/-- The zeros and the status 2, for `d ≤ 2^(8 pl)`. -/
theorem outsRes_zeros {I : KIn} {s t : State} {d : Nat}
    (hd : Spec.Rsa.inverse I.E I.L = some d) (hsm : d ≤ 2 ^ (8 * I.pl)) (Z : ZerosPost I s t) :
    OutsRes I t.mem (t.gpr .rax) := by
  have hr : keyFromPrimes (16 * I.pl) I.E I.P₀ I.Q₀ = .inr () := by
    unfold keyFromPrimes
    have hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
      by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
    rw [hswap]
    dsimp only
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, show 16 * I.pl / 2 = 8 * I.pl by omega]
    dsimp only
    rw [ite_eq_left hsm]
  rw [OutsRes, keyOp_inr hr, Z.1]
  exact ⟨by decide, Z.2.1⟩

theorem i2osp_zero (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  simp [Spec.Rsa.i2osp, List.map_const']

theorem i2osp_ite (c : Bool) (x k : Nat) :
    Spec.Rsa.i2osp (if c then x else 0) k = if c then Spec.Rsa.i2osp x k else List.replicate k 0 := by
  cases c <;> simp [i2osp_zero]

/-- The outputs and the status of `keyPart`, for `d > 2^(8 pl)` or no `d`. -/
theorem outsRes_tail {I : KIn} {s t : State} (L : KLens I) {ok : Bool}
    (hok : (∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true)
    (hdd : ∀ d, Spec.Rsa.inverse I.E I.L = some d → av I s.mem aDd = d)
    (hb : (decide (av I s.mem aDd ≤ 2 ^ (8 * I.pl)) && ok) = false) (T : TailPost I s t ok) :
    OutsRes I t.mem (t.gpr .rax) := by
  obtain ⟨x, hx, hxl, ⟨hax, hN, hD, hP, hQ, hDp, hDq, hQi⟩, -⟩ := T
  have he : I.E < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
  have hk := keyFromPrimes_code (x := x) L.pl1 L.pl2 (lt_of_os2ip_len L.pbl) (lt_of_os2ip_len L.qbl) he hx hxl
  have hW : 64 * I.W - 1 = 16 * I.pl - 1 := by rw [L.W]; have := L.pl8; omega
  simp only [finalOk, hW] at hax hN hD hP hQ hDp hDq hQi
  have hstat : ∀ c : Bool, ((BitVec.ofNat 64 c.toNat).setWidth 32).toNat = c.toNat := fun c =>
    setWidth32 _ (by cases c <;> decide)
  rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
  · have hok' : ok = false := by
      cases ok
      · rfl
      · obtain ⟨d, hd⟩ := hok.mpr rfl; rw [hi] at hd; cases hd
    subst hok'
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    rw [OutsRes, keyOp_error hk, hax, hstat]
    refine ⟨rfl, ?_⟩
    simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
  · have hok' : ok = true := hok.mp ⟨d, hi⟩
    subst hok'
    have hd := hdd d hi
    rw [hd, Bool.and_true, decide_eq_false_iff_not] at hb
    have hd2 : 2 ≤ d := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 8 * I.pl by have := L.pl1; omega)
      omega
    have hqp : I.Q ≤ I.P := by simp only [KIn.P, KIn.Q]; split <;> omega
    obtain ⟨hP3, hQ2, -⟩ := primes_of_inverse hqp hi hd2
    have hdvP : dv (I.P - 1) = I.P - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega
    have hdvQ : dv (I.Q - 1) = I.Q - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega
    simp only [Bool.and_true, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hb)] at hk
    simp only [hd, hdvP, hdvQ] at hD hDp hDq
    generalize hc : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qMod I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c
      at hax hN hD hP hQ hDp hDq hQi
    have hc' : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qModP I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c := hc
    rw [hc'] at hk
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk
      rw [OutsRes, keyOp_error hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, i2osp_zero] at hN hD hP hQ hDp hDq hQi
      exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
    · simp only [↓reduceIte] at hk hN hD hP hQ hDp hDq hQi
      rw [OutsRes, keyOp_ok hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.map_cons, List.map_nil, hN, hD, hP, hQ, hDp, hDq, hQi]

end VG.Proof.RsaKeyGen.X86_64.Key
