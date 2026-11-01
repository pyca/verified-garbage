module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Stores
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Init
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.DMath
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Primes
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.DPart
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Tail
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads

/-!
# `vg_rsa_keygen_key` on PPC64LE: the body

`body_ok`: from the entry's state, the phases in order (`Init.lean`,
`Primes.lean`, `Lcm.lean`, `DPart.lean`, `Tail.lean`, `Stores.lean`): the
status `2 small + mask` in `r3` and the seven outputs under the mask, with
the arrays they come from holding `n = p q`, `d`, `p`, `q`, `dP`, `dQ` and
`qInv` (`BodyPost`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs aZero)
open VG.Impl.RsaKeyGen.PPC64LE.Key (body setup loads consts primes lcmPart dPart smallPart qinvPart crtPart
  nPart maskPart stores nArr aOne aTwo aThree aTop aC aC33 aE aP0 aQ0 aP aQ aPm aQm aL aD aDP aDQ aQi aN
  X0 X1 X3 X5 X6 X7 X8)
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The primes, ordered, and `L = lcm(p - 1, q - 1)`. -/
abbrev kP (s0 : State) : Nat := if pIn s0 < qIn s0 then qIn s0 else pIn s0
abbrev kQ (s0 : State) : Nat := if pIn s0 < qIn s0 then pIn s0 else qIn s0
abbrev kLc (s0 : State) : Nat := Nat.lcm (kP s0 - 1) (kQ s0 - 1)

/-- `d` exists and is at most `2^(8 p_len)`: the status 2. -/
def kSmall (s0 : State) (D : Nat) : Prop := okv (eIn s0) (kLc s0) ∧ D < 2 ^ (8 * kL s0) + 1

/-- The mask under which the outputs are written. -/
def kMask (s0 : State) (D : Nat) : Prop :=
  ¬ kSmall s0 D ∧ ¬ kP s0 * kQ s0 < 2 ^ (16 * kL s0 - 1) ∧ okv (eIn s0) (kLc s0) ∧
    Nat.gcd (kQ s0) (mL (kP s0)) = 1 ∧ kP s0 % 2 = 1 ∧ kQ s0 % 2 = 1 ∧ eIn s0 % 2 = 1 ∧ ¬ eIn s0 < 3 ∧
    eIn s0 < 2 ^ 33

instance (s0 : State) (D : Nat) : Decidable (kSmall s0 D) := by unfold kSmall; infer_instance
instance (s0 : State) (D : Nat) : Decidable (kMask s0 D) := by unfold kMask; infer_instance

/-- The registers the body changes. -/
abbrev bodyAll : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r29, .r30]

/-- What the body establishes. -/
def BodyPost (s0 t : State) : Prop :=
  ∃ m D x, Fr s0 m t ∧ D < 2 ^ (32 * kW s0) ∧ x < mL (kP s0) ∧
    ((mL (kP s0) : Nat) : Int) ∣ (x : Int) * kQ s0 - Nat.gcd (kQ s0) (mL (kP s0)) ∧
    (okv (eIn s0) (kLc s0) → Spec.Rsa.inverse (eIn s0) (kLc s0) = some D) ∧
    t.gpr .r3 = BitVec.ofNat 64 (2 * (if kSmall s0 D then 1 else 0) + (if kMask s0 D then 1 else 0)) ∧
    Outs s0 m (decide (kMask s0 D)) t.mem (outList s0) ∧
    num m (kB s0) (kW s0) aN = kP s0 * kQ s0 ∧ num m (kB s0) (kW s0) aD = D ∧
    num m (kB s0) (kW s0) aP = kP s0 ∧ num m (kB s0) (kW s0) aQ = kQ s0 ∧
    num m (kB s0) (kW s0) aDP = D % (if kP s0 - 1 = 0 then 1 else kP s0 - 1) ∧
    num m (kB s0) (kW s0) aDQ = D % (if kQ s0 - 1 = 0 then 1 else kQ s0 - 1) ∧
    num m (kB s0) (kW s0) aQi = x

theorem body_eq : body = seqs (setup :: loads :: (consts ++ [primes, lcmPart, dPart, smallPart, qinvPart,
    crtPart, nPart, maskPart, stores])) := rfl

theorem flag_le {c : Prop} [Decidable c] {x : Nat} (h : x = if c then 1 else 0) : x ≤ 1 := by
  rw [h]; exact flag01 _

theorem slot_flag {m : Mem} {B : Addr} {d x : Nat} {c : Prop} [Decidable c] (h : slot m B d = x)
    (hx : x = if c then 1 else 0) : slot m B d = if decide c then 1 else 0 := by
  rw [h, hx]; by_cases hc : c <;> simp [hc]

theorem body_ok [InvLaw] {s0 s : State} (h : Base s0 s) (ha : Args s0 s) :
    WP isa body s fun t => BodyPost s0 t ∧ Keep bodyAll s t := by
  have p := kpre h.pre
  obtain ⟨-, hw16, hw256, hlw, h4⟩ := pre_ws h.pre
  have l1 := p.l1
  have l2 := p.l2
  have el8 := p.el8
  have hpl : pIn s0 < 2 ^ (8 * kL s0) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0))
    rw [show (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0)).length = kL s0 by simp [Spec.Rsa.bytesAt]] at this
    rw [Nat.pow_mul]; exact this
  have hql : qIn s0 < 2 ^ (8 * kL s0) := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0))
    rw [show (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0)).length = kL s0 by simp [Spec.Rsa.bytesAt]] at this
    rw [Nat.pow_mul]; exact this
  have hel : eIn s0 < 2 ^ 64 := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (PPC64LE.stackArg s0 7).toNat)
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact Nat.lt_of_lt_of_le this (by
      rw [show (2 : Nat) ^ 64 = 256 ^ 8 by decide]; exact Nat.pow_le_pow_right (by decide) el8)
  have hW : 32 * kW s0 = 16 * kL s0 := by omega_arith
  rw [body_eq, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h ha.r22) fun t1 ⟨b1, w1, k1, r1⟩ => ?_
  have a1 := ha.of_keep r1
  rw [wp_seqs_cons (by simp [consts])]
  refine WP.mono (loads_ok b1 a1 w1 k1 rfl rfl rfl) fun t2 ⟨b2, w2, ⟨V2, k2, o2, eP, eQ, eE⟩, r2⟩ => ?_
  have a2 := a1.of_keep r2
  rw [wp_seqs_append (by simp [consts]) (List.cons_ne_nil _ _)]
  refine WP.mono (consts_ok b2 a2 w2 k2 (by rw [o2 _ (by decide) (by decide) (by decide)])
    (by rw [o2 _ (by decide) (by decide) (by decide)]) (by rw [o2 _ (by decide) (by decide) (by decide)])
    (by rw [o2 _ (by decide) (by decide) (by decide)]) (by rw [o2 _ (by decide) (by decide) (by decide)])
    (by rw [o2 _ (by decide) (by decide) (by decide)]))
    fun t3 ⟨b3, w3, ⟨V3, k3, o3, one3, two3, three3, c3, c33, top3⟩, r3⟩ => ?_
  have a3 := a2.of_keep r3
  have zero3 : V3 aZero = 0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      o2 _ (by decide) (by decide) (by decide)]
  have p3 : V3 aP0 = pIn s0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eP]
  have q3 : V3 aQ0 = qIn s0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eQ]
  have e3 : V3 aE = eIn s0 := by
    rw [o3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), eE]
  -- The primes.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (primes_ok w3 k3 one3 zero3) fun t4 ⟨w4, ⟨V4, F4, k4, o4, p4, vP, vQ, vPm, vQm⟩, f4, r4⟩ => ?_
  have b4 := b3.of_phase f4 r4
  have a4 := a3.of_keep r4
  rw [p3, q3] at vP vQ
  rw [vP] at vPm
  rw [vQ] at vQm
  have hP : kP s0 < 2 ^ (8 * kL s0) := by simp only [kP]; split <;> with_reducible assumption
  have hQ : kQ s0 < 2 ^ (8 * kL s0) := by simp only [kQ]; split <;> with_reducible assumption
  -- `L`.
  have h22 : t4.gpr .r22 = BitVec.ofNat 64 (kL s0) := by
    rw [a4.r22]; exact VG.Proof.Rsa.PPC64LE.CrtValues.ofNat_toNat64 _
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (lcmPart_ok w4 k4 h22 (by omega_arith) (by omega_arith) hW (by omega_arith) h4 (by rw [vPm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hP)
    (by rw [vQm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hQ)
    (by vsimp [o4, one3]) (by vsimp [o4, o3, two3]) (by vsimp [o4, three3]) (by vsimp [o4, zero3]))
    fun t5 ⟨w5, ⟨V5, F5, k5, o5, p5, vL⟩, f5, r5⟩ => ?_
  have b5 := b4.of_phase f5 r5
  have a5 := a4.of_keep r5
  rw [vPm, vQm] at vL
  -- `d`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dPart_ok w5 k5 (by omega_arith) (by vsimp [o5, o4, e3]; exact hel) (by vsimp [o5, o4, one3])
    (by vsimp [o5, o4, two3]) (by vsimp [o5, o4, three3]) (by vsimp [o5, o4, zero3]))
    fun t6 ⟨w6, ⟨V6, F6, k6, o6, p6, x3, x5, x6, vD⟩, f6, r6⟩ => ?_
  have b6 := b5.of_phase f6 r6
  have a6 := a5.of_keep r6
  have eE5 : V5 aE = eIn s0 := by vsimp [o5, o4, e3]
  simp only [eE5, vL] at x3 x5 x6 vD
  -- Small.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (smallPart_ok w6 k6 (flag_le x6)) fun t7 ⟨w7, ⟨V7, F7, k7, o7, p7, x7⟩, f7, r7⟩ => ?_
  have b7 := b6.of_phase f7 r7
  have a7 := a6.of_keep r7
  have vC6 : V6 aC = 2 ^ (8 * kL s0) + 1 := by vsimp [o6, o5, o4, c3]
  simp only [x6, vC6] at x7
  -- `qInv`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have vP7 : V7 aP = kP s0 := by vsimp [o7, o6, o5, vP]
  have vQ7 : V7 aQ = kQ s0 := by vsimp [o7, o6, o5, vQ]
  refine WP.mono (qinvPart_ok w7 k7 (by vsimp [o7, o6, o5, o4, one3]) (by vsimp [o7, o6, o5, o4, three3])
    (by vsimp [o7, o6, o5, o4, zero3]) (by omega_arith) (by rw [a7.r22, ← a4.r22]; exact h22) (by omega_arith) h4
    (by omega_arith) (by omega_arith) (by rw [vP7]; exact hP) (by rw [vQ7]; exact hQ)) fun t8 ⟨w8, ⟨V8, F8, k8, o8, p8, y0, y1, xl, xd⟩, f8, r8⟩ => ?_
  have b8 := b7.of_phase f8 r8
  have a8 := a7.of_keep r8
  simp only [vP7, vQ7] at y0 y1 xl xd
  -- `dP`, `dQ`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (crtPart_ok w8 k8 (by vsimp [o8, o7, o6, o5, o4, one3]) (by vsimp [o8, o7, o6, o5, o4, zero3]))
    fun t9 ⟨w9, ⟨V9, F9, k9, o9, p9, vDP, vDQ⟩, f9, r9⟩ => ?_
  have b9 := b8.of_phase f9 r9
  have a9 := a8.of_keep r9
  -- `n`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have vP9 : V9 aP = kP s0 := by vsimp [o9, o8, vP7]
  have vQ9 : V9 aQ = kQ s0 := by vsimp [o9, o8, vQ7]
  refine WP.mono (nPart_ok w9 k9 (by rw [a9.r22, ← a4.r22]; exact h22) (by omega_arith) (by omega_arith) hW
    (by rw [vP9]; exact hP) (by rw [vQ9]; exact hQ) (by vsimp [o9, o8, o7, o6, o5, o4, zero3]))
    fun t10 ⟨w10, ⟨V10, k10, o10, vN⟩, f10, r10⟩ => ?_
  have b10 := b9.of_phase f10 r10
  have a10 := a9.of_keep r10
  simp only [vP9, vQ9] at vN
  -- The mask.
  have g0 : F9 X0 = kP s0 % 2 := by vsimp [p9, y0]
  have g1 : F9 X1 = if Nat.gcd (kQ s0) (mL (kP s0)) = 1 then 1 else 0 := by vsimp [p9, y1]
  have g3 : F9 X3 = eIn s0 % 2 := by vsimp [p9, p8, p7, x3]
  have g5 : F9 X5 = if eIn s0 < 3 then 1 else 0 := by vsimp [p9, p8, p7, x5]
  have g6 : F9 X6 = if okv (eIn s0) (kLc s0) then 1 else 0 := by vsimp [p9, p8, p7, x6]
  have g7 : F9 X7 = if (if okv (eIn s0) (kLc s0) then 1 else 0) = 1 ∧ V6 aD < 2 ^ (8 * kL s0) + 1 then 1 else 0 := by
    vsimp [p9, p8, x7]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (maskPart_ok w10 k10 (by rw [g0]; omega_arith) (flag_le g1) (by rw [g3]; omega_arith) (flag_le g5)
    (flag_le g6) (flag_le g7)) fun t11 ⟨w11, ⟨V11, F11, k11, o11, p11, x8⟩, f11, r11⟩ => ?_
  have b11 := b10.of_phase f11 r11
  have a11 := a10.of_keep r11
  have vD9 : V9 aD = V6 aD := by vsimp [o9, o8, o7]
  have vN10 : V10 aN = kP s0 * kQ s0 := vN
  have vTop : V10 aTop = 2 ^ (16 * kL s0 - 1) := by vsimp [o10, o9, o8, o7, o6, o5, o4, top3]; rw [hW]
  have vE : V10 aE = eIn s0 := by vsimp [o10, o9, o8, o7, o6, eE5]
  have vC33 : V10 aC33 = 2 ^ 33 := by vsimp [o10, o9, o8, o7, o6, o5, o4, c33]
  have vQ10 : V10 aQ = kQ s0 := by vsimp [o10, vQ9]
  simp only [vN10, vTop, vE, vC33, vQ10, g0, g1, g3, g5, g6, g7] at x8
  have sm : (if (if okv (eIn s0) (kLc s0) then 1 else 0) = 1 ∧ V6 aD < 2 ^ (8 * kL s0) + 1 then 1 else 0) =
      if kSmall s0 (V6 aD) then 1 else 0 := by
    unfold kSmall; by_cases o : okv (eIn s0) (kLc s0) <;> simp [o]
  have mk : F11 X8 = if kMask s0 (V6 aD) then 1 else 0 := by
    rw [x8, sm]; unfold kMask
    simp only [flag_one, flag_zero]
  have s7 : F11 X7 = if kSmall s0 (V6 aD) then 1 else 0 := by vsimp [p11]; rw [g7, sm]
  -- The stores.
  refine WP.mono (stores_ok b11 a11 w11 (a := decide (kSmall s0 (V6 aD))) (b := decide (kMask s0 (V6 aD)))
    (slot_flag (k11.flg X7 (by decide)) s7) (slot_flag (k11.flg X8 (by decide)) mk))
    fun t ⟨ft, t3, outs, kt⟩ => ⟨⟨t11.mem, V6 aD, V8 aQi, ft, ?_, xl, xd, vD, ?_, outs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_⟩
  · exact k6.lt (by decide)
  · rw [t3]; simp only [decide_eq_true_eq]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, vN10]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vD9]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vP9]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, vQ10]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vDP, o8, o7, o6, o5, vPm]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, vDQ, o8, o7, o6, o5, vQm]
  · rw [k11.arrs _ (by decide)]; vsimp [o11, o10, o9]
  · exact (((((((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans
      r10).trans r11).trans kt).mono

end VG.Proof.RsaKeyGen.PPC64LE.Key
