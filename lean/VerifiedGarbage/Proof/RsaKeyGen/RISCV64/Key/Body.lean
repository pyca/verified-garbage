module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Stores
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.DPart
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.KTail
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: the body

`body_ok`: from the entry's state, the phases in order (`Init.lean`,
`Lcm.lean`, `DPart.lean`, `KTail.lean`, `Stores.lean`): the status
`2 small + mask` in `a0` and the seven outputs under the mask, with the
arrays they come from holding `n = p q`, `d`, `p`, `q`, `dP`, `dQ` and
`qInv` (`BodyPost`), as PPC64LE's (`Proof/RsaKeyGen/PPC64LE/Key/Body.lean`).
-/

-- separate module: the body's chaining is not re-checked with every change to the correctness proof

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs aZero)
open VG.Impl.RsaKeyGen.RISCV64.Key (body setup loads consts primes lcmPart dPart smallPart qinvPart crtPart
  nPart maskPart stores nArr aOne aTwo aThree aTop aC aC33 aE aP0 aQ0 aP aQ aPm aQm aL aDv aD aDP aDQ aQi aN
  X0 X1 X3 X5 X6 X7 X8)

/-- The inputs as numbers. -/
abbrev pIn (s0 : State) : Nat := Spec.Rsa.os2ip (pB s0)
abbrev qIn (s0 : State) : Nat := Spec.Rsa.os2ip (qB s0)
abbrev eIn (s0 : State) : Nat := Spec.Rsa.os2ip (eB s0)

/-- The primes, ordered, and `L = lcm(p - 1, q - 1)`. -/
abbrev kP (s0 : State) : Nat := if pIn s0 < qIn s0 then qIn s0 else pIn s0
abbrev kQ (s0 : State) : Nat := if pIn s0 < qIn s0 then pIn s0 else qIn s0
abbrev kLc (s0 : State) : Nat := Nat.lcm (kP s0 - 1) (kQ s0 - 1)

/-- `d` exists and is at most `2^(8 p_len)`: the status 2. -/
def kSmall (s0 : State) (D : Nat) : Prop := okv (eIn s0) (kLc s0) ∧ D < 2 ^ (8 * pLen s0) + 1

/-- The mask under which the outputs are written. -/
def kMask (s0 : State) (D : Nat) : Prop :=
  ¬ kSmall s0 D ∧ ¬ kP s0 * kQ s0 < 2 ^ (16 * pLen s0 - 1) ∧ okv (eIn s0) (kLc s0) ∧
    Nat.gcd (kQ s0) (mL (kP s0)) = 1 ∧ kP s0 % 2 = 1 ∧ kQ s0 % 2 = 1 ∧ eIn s0 % 2 = 1 ∧ ¬ eIn s0 < 3 ∧
    eIn s0 < 2 ^ 33

instance (s0 : State) (D : Nat) : Decidable (kSmall s0 D) := by unfold kSmall; infer_instance
instance (s0 : State) (D : Nat) : Decidable (kMask s0 D) := by unfold kMask; infer_instance

/-- What the body establishes. -/
def BodyPost (s0 t : State) : Prop :=
  ∃ m D x, CE s0 t ∧ D < 2 ^ (64 * wOf s0) ∧ x < mL (kP s0) ∧
    ((mL (kP s0) : Nat) : Int) ∣ (x : Int) * kQ s0 - Nat.gcd (kQ s0) (mL (kP s0)) ∧
    (okv (eIn s0) (kLc s0) → Spec.Rsa.inverse (eIn s0) (kLc s0) = some D) ∧
    t.gpr .a0 = BitVec.ofNat 64 (2 * (if kSmall s0 D then 1 else 0) + (if kMask s0 D then 1 else 0)) ∧
    Outs s0 m (decide (kMask s0 D)) t.mem (outList s0) ∧
    num m (bOf s0) (wOf s0) aN = kP s0 * kQ s0 ∧ num m (bOf s0) (wOf s0) aD = D ∧ num m (bOf s0) (wOf s0) aP = kP s0 ∧ num m (bOf s0) (wOf s0) aQ = kQ s0 ∧
    num m (bOf s0) (wOf s0) aDP = D % (if kP s0 - 1 = 0 then 1 else kP s0 - 1) ∧
    num m (bOf s0) (wOf s0) aDQ = D % (if kQ s0 - 1 = 0 then 1 else kQ s0 - 1) ∧ num m (bOf s0) (wOf s0) aQi = x

theorem body_eq : body = seqs (setup :: loads :: (consts ++ [primes, lcmPart, dPart, smallPart, qinvPart,
    crtPart, nPart, maskPart, stores])) := rfl

theorem flag_le {c : Prop} [Decidable c] {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  rw [h]; exact flag01 _

theorem slot_flag {m : Mem} {B : Addr} {d x : Nat} {c : Prop} [Decidable c] (h : slot m B d = x)
    (hx : x = if c then 1 else 0) : slot m B d = if decide c then 1 else 0 := by
  rw [h, hx]; by_cases hc : c <;> simp [hc]

theorem pIn_lt (s0 : State) : pIn s0 < 2 ^ (8 * pLen s0) := os2ip_bytes_lt _ _ _

theorem qIn_lt (s0 : State) : qIn s0 < 2 ^ (8 * pLen s0) := os2ip_bytes_lt _ _ _

theorem eIn_lt {s0 : State} (h : PreC s0) : eIn s0 < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (os2ip_bytes_lt _ _ _) (Nat.pow_le_pow_right (by decide) (by have := h.e2; omega))

theorem kP_lt (s0 : State) : kP s0 < 2 ^ (8 * pLen s0) := by
  have := pIn_lt s0; have := qIn_lt s0; simp only [kP]; split <;> with_reducible assumption

theorem kQ_lt (s0 : State) : kQ s0 < 2 ^ (8 * pLen s0) := by
  have := pIn_lt s0; have := qIn_lt s0; simp only [kQ]; split <;> with_reducible assumption

/-- From the entry to the constants, the primes and `L`: `KE` with the values the later phases need. -/
theorem front_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa (seqs (setup :: loads :: (consts ++ [primes, lcmPart]))) s fun t =>
      St s0 allArrs t ∧ word t.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0 ∧
      num t.mem (bOf s0) (wOf s0) aOne = 1 ∧ num t.mem (bOf s0) (wOf s0) aTwo = 2 ∧ num t.mem (bOf s0) (wOf s0) aThree = 3 ∧ num t.mem (bOf s0) (wOf s0) aZero = 0 ∧
      num t.mem (bOf s0) (wOf s0) aC = 2 ^ (8 * pLen s0) + 1 ∧ num t.mem (bOf s0) (wOf s0) aC33 = 2 ^ 33 ∧
      num t.mem (bOf s0) (wOf s0) aTop = 2 ^ (16 * pLen s0 - 1) ∧ num t.mem (bOf s0) (wOf s0) aE = eIn s0 ∧ num t.mem (bOf s0) (wOf s0) aP = kP s0 ∧
      num t.mem (bOf s0) (wOf s0) aQ = kQ s0 ∧ num t.mem (bOf s0) (wOf s0) aPm = kP s0 - 1 ∧ num t.mem (bOf s0) (wOf s0) aQm = kQ s0 - 1 ∧
      num t.mem (bOf s0) (wOf s0) aL = kLc s0 := by
  have w4 := h.wOf_eq
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h c) fun t1 c1 => ?_
  rw [wp_seqs_cons (by simp [consts])]
  refine WP.mono (loads_ok h c1) fun t2 ⟨c2, eP, eQ, eE⟩ => ?_
  rw [wp_seqs_append (by simp [consts]) (List.cons_ne_nil _ _)]
  refine WP.mono (consts_ok h c2 (by decide)) fun t3 ⟨c3, k3, o3⟩ => ?_
  have zero3 : num t3.mem (bOf s0) (wOf s0) aZero = 0 := c3.zero (by decide) (by decide)
  have p3 : num t3.mem (bOf s0) (wOf s0) aP0 = pIn s0 := by rw [o3 _ (by decide) (by decide), eP]
  have q3 : num t3.mem (bOf s0) (wOf s0) aQ0 = qIn s0 := by rw [o3 _ (by decide) (by decide), eQ]
  have e3 : num t3.mem (bOf s0) (wOf s0) aE = eIn s0 := by rw [o3 _ (by decide) (by decide), eE]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (primes_ok c3 k3.one zero3) fun t4 ⟨c4, o4, vP, vQ, vPm, vQm⟩ => ?_
  simp only [nm] at o4 vP vQ vPm vQm
  rw [p3, q3] at vP vQ
  rw [vP] at vPm
  rw [vQ] at vQm
  have hP := kP_lt s0
  have hQ := kQ_lt s0
  rw [show seqs [lcmPart] = lcmPart from rfl]
  refine WP.mono (lcmPart_ok h c4 ((o4 _ (by decide) (by decide)).trans k3.one)
    ((o4 _ (by decide) (by decide)).trans k3.two) ((o4 _ (by decide) (by decide)).trans k3.three)
    ((o4 _ (by decide) (by decide)).trans zero3) (by simp only [nm]; rw [vPm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hP)
    (by simp only [nm]; rw [vQm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hQ)
    (c4.word_zero (by decide) (by decide) (by omega))) fun t ⟨c5, o5, vL, dv⟩ => ?_
  simp only [nm] at o5 vL
  have k : ∀ j < nArr, j ∉ VG.Proof.RsaKeyGen.RISCV64.Key.lcmArrs → j ∉ primesArrs →
      num t.mem (bOf s0) (wOf s0) j = num t3.mem (bOf s0) (wOf s0) j := fun j hj h5 h4 => by rw [o5 j hj h5, o4 j hj h4]
  have h64 : 64 * wOf s0 = 16 * pLen s0 := by omega
  refine ⟨c5.all, dv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k _ (by decide) (by decide) (by decide)]; exact k3.one
  · rw [k _ (by decide) (by decide) (by decide)]; exact k3.two
  · rw [k _ (by decide) (by decide) (by decide)]; exact k3.three
  · rw [k _ (by decide) (by decide) (by decide)]; exact zero3
  · rw [k _ (by decide) (by decide) (by decide)]; exact k3.c
  · rw [k _ (by decide) (by decide) (by decide)]; exact k3.c33
  · rw [k _ (by decide) (by decide) (by decide), k3.top, h64]
  · rw [k _ (by decide) (by decide) (by decide)]; exact e3
  · rw [o5 _ (by decide) (by decide)]; exact vP
  · rw [o5 _ (by decide) (by decide)]; exact vQ
  · rw [o5 _ (by decide) (by decide)]; exact vPm
  · rw [o5 _ (by decide) (by decide)]; exact vQm
  · rw [vL, vPm, vQm]

theorem body_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) :
    WP isa body s (BodyPost s0) := by
  have hpl := kP_lt s0
  have hql := kQ_lt s0
  have hel := eIn_lt h
  rw [body_eq, show setup :: loads :: (consts ++ [primes, lcmPart, dPart, smallPart, qinvPart, crtPart, nPart,
    maskPart, stores]) = (setup :: loads :: (consts ++ [primes, lcmPart])) ++
      [dPart, smallPart, qinvPart, crtPart, nPart, maskPart, stores] by simp,
    wp_seqs_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)]
  refine WP.mono (front_ok h c) fun t5 ⟨c5, dv, one5, two5, three5, zero5, c5', c335, top5, e5, p5, q5, pm5,
    qm5, l5⟩ => ?_
  have k5 := KE.of_st c5 dv
  -- `d`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dPart_ok h k5 (by rw [e5]; exact hel) one5 two5 three5 zero5)
    fun t6 ⟨V6, F6, k6, o6, p6, x3, x5, x6, vD⟩ => ?_
  simp only [e5, l5] at x3 x5 x6 vD
  -- Small.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (smallPart_ok k6 (flag_le x6)) fun t7 ⟨V7, F7, k7, o7, p7, x7⟩ => ?_
  have vC6 : V6 aC = 2 ^ (8 * pLen s0) + 1 := by vsimp [o6, c5']
  simp only [x6, vC6] at x7
  -- `qInv`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have vP7 : V7 aP = kP s0 := by vsimp [o7, o6, p5]
  have vQ7 : V7 aQ = kQ s0 := by vsimp [o7, o6, q5]
  refine WP.mono (qinvPart_ok h k7 (by vsimp [o7, o6, one5]) (by vsimp [o7, o6, three5])
    (by vsimp [o7, o6, zero5]) (by rw [vP7]; exact hpl) (by rw [vQ7]; exact hql))
    fun t8 ⟨V8, F8, k8, o8, p8, y0, y1, xl, xd⟩ => ?_
  simp only [vP7, vQ7] at y0 y1 xl xd
  -- `dP`, `dQ`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (crtPart_ok k8 (by vsimp [o8, o7, o6, one5]) (by vsimp [o8, o7, o6, zero5]))
    fun t9 ⟨V9, F9, k9, o9, p9, vDP, vDQ⟩ => ?_
  -- `n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have vP9 : V9 aP = kP s0 := by vsimp [o9, o8, vP7]
  have vQ9 : V9 aQ = kQ s0 := by vsimp [o9, o8, vQ7]
  refine WP.mono (nPart_ok h k9 (by rw [vP9]; exact hpl) (by rw [vQ9]; exact hql)
    (by vsimp [o9, o8, o7, o6, zero5])) fun t10 ⟨V10, k10, o10, vN⟩ => ?_
  simp only [vP9, vQ9] at vN
  -- The mask.
  have g0 : F9 X0 = kP s0 % 2 := by vsimp [p9, y0]
  have g1 : F9 X1 = if Nat.gcd (kQ s0) (mL (kP s0)) = 1 then 1 else 0 := by vsimp [p9, y1]
  have g3 : F9 X3 = eIn s0 % 2 := by vsimp [p9, p8, p7, x3]
  have g5 : F9 X5 = if eIn s0 < 3 then 1 else 0 := by vsimp [p9, p8, p7, x5]
  have g6 : F9 X6 = if okv (eIn s0) (kLc s0) then 1 else 0 := by vsimp [p9, p8, p7, x6]
  have g7 : F9 X7 = if (if okv (eIn s0) (kLc s0) then 1 else 0) = 1 ∧ V6 aD < 2 ^ (8 * pLen s0) + 1
      then 1 else 0 := by
    vsimp [p9, p8, x7]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (maskPart_ok k10 (by rw [g0]; omega) (flag_le g1) (by rw [g3]; omega) (flag_le g5)
    (flag_le g6) (flag_le g7)) fun t11 ⟨V11, F11, k11, o11, p11, x8⟩ => ?_
  have vD9 : V9 aD = V6 aD := by vsimp [o9, o8, o7]
  have vTop : V10 aTop = 2 ^ (16 * pLen s0 - 1) := by vsimp [o10, o9, o8, o7, o6, top5]
  have vE : V10 aE = eIn s0 := by vsimp [o10, o9, o8, o7, o6, e5]
  have vC33 : V10 aC33 = 2 ^ 33 := by vsimp [o10, o9, o8, o7, o6, c335]
  have vQ10 : V10 aQ = kQ s0 := by vsimp [o10, vQ9]
  simp only [vN, vTop, vE, vC33, vQ10, g0, g1, g3, g5, g6, g7] at x8
  have sm : (if (if okv (eIn s0) (kLc s0) then 1 else 0) = 1 ∧ V6 aD < 2 ^ (8 * pLen s0) + 1 then 1 else 0) =
      if kSmall s0 (V6 aD) then 1 else 0 := by
    unfold kSmall; by_cases o : okv (eIn s0) (kLc s0) <;> simp [o]
  have mk : F11 X8 = if kMask s0 (V6 aD) then 1 else 0 := by
    rw [x8, sm]; unfold kMask
    simp only [flag_one, flag_zero]
  have s7 : F11 X7 = if kSmall s0 (V6 aD) then 1 else 0 := by vsimp [p11]; rw [g7, sm]
  -- The stores.
  rw [show seqs [stores] = stores from rfl]
  refine WP.mono (stores_ok h (Fr.of_st k11.st) (a := decide (kSmall s0 (V6 aD))) (b := decide (kMask s0 (V6 aD)))
    (slot_flag (k11.flg X7 (by decide)) s7) (slot_flag (k11.flg X8 (by decide)) mk))
    fun t ⟨ce, t0, outs⟩ => ⟨t11.mem, V6 aD, V8 aQi, ce, k6.lt (by decide), xl, xd, vD, ?_, outs, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · rw [t0]; simp only [decide_eq_true_eq]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, vN]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vD9]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vP9]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, vQ10]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vDP, o8, o7, o6, pm5]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vDQ, o8, o7, o6, qm5]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, o9]

end VG.Proof.RsaKeyGen.RISCV64.Key
