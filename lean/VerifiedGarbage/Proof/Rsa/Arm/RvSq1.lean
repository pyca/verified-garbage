module
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.RecoverExp

import VerifiedGarbage.Proof.Rsa.Arm.RvTaint3
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads

/-! # `vg_rsa_recover_primes` on ARMv7: the masks of a squaring (`St.pmasks`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- A recorded header word, as a word. -/
theorem KS.readSlot (h : KS P σ A live AW liveW V ls s) {d : Nat} (hd : d ∈ ls) :
    s.mem.readW (off (State.addr P.B) d) 32 = BitVec.ofNat 32 (V d) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← h.sl d hd, Nat.mod_eq_of_lt (BitVec.isLt _)]

end

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- The masks of a squaring, from `k`, `t`, `done`, `ok`, `x = 1` and `x = -1`. -/
theorem St.pmasks {kf tf : State → Nat} {dn ok e1 e2 : State → Bool}
    (hls : sK ∈ LS ∧ sTc ∈ LS ∧ sDone ∈ LS ∧ sOk ∈ LS ∧ sE1 ∈ LS ∧ sE2 ∈ LS)
    (hv : ∀ σ, E σ → kf σ + 1 < 2 ^ 31 ∧ tf σ < 2 ^ 31 ∧ V σ sK = kf σ ∧ V σ sTc = tf σ ∧
      V σ sDone = b2n (dn σ) ∧ V σ sOk = b2n (ok σ) ∧ V σ sE1 = b2n (e1 σ) ∧ V σ sE2 = b2n (e2 σ)) :
    VP (St P E A L AW LW V LS P.w nArr) (.block sqMasks)
      (St P E A L AW LW (fun σ => upd (upd (upd (V σ) sOk
          (b2n (ok σ || (!dn σ && decide (kf σ < tf σ) && e1 σ)))) sDone
          (b2n (dn σ || (!dn σ && decide (kf σ < tf σ) && (e1 σ || (e2 σ || decide (kf σ + 1 = tf σ))))))) sLive
          (b2n (!dn σ && decide (kf σ < tf σ) && !e1 σ && !(e2 σ || decide (kf σ + 1 = tf σ)))))
        (sLive :: sDone :: sOk :: LS) P.w nArr) := by
  refine VP.ctx sqMasks_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  obtain ⟨hk, ht, vK, vT, vD, vO, vE1, vE2⟩ := hv σ e
  obtain ⟨lK, lT, lD, lO, lE1, lE2⟩ := hls
  have hz := hdr_Z h.sizes
  unfold sqMasks
  refine wp_ldrSlot hw (d := sK) (by decide) fun s1 u1 => ?_
  have w1 := hw.of_upd u1 (by decide) (by decide) (by decide)
  refine wp_ldrSlot w1 (d := sTc) (by decide) fun s2 u2 => ?_
  have w2 := w1.of_upd u2 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  have w3 := w2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  have w4 := w3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_ldrSlot w4 (d := sDone) (by decide) fun s5 u5 => ?_
  have w5 := w4.of_upd u5 (by decide) (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  have w6 := w5.of_upd u6 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  have w7 := w6.of_upd u7 (by decide) (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s8 u8 => ?_
  have w8 := w7.of_upd u8 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  have w9 := w8.of_upd u9 (by decide) (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s10 u10 => ?_
  have w10 := w9.of_upd u10 (by decide) (by decide) (by decide)
  refine wp_mov (op2_lsr (by decide)) fun s11 u11 => ?_
  have w11 := w10.of_upd u11 (by decide) (by decide) (by decide)
  refine wp_ldrSlot w11 (d := sE2) (by decide) fun s12 u12 => ?_
  have w12 := w11.of_upd u12 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s13 u13 => ?_
  have w13 := w12.of_upd u13 (by decide) (by decide) (by decide)
  refine wp_ldrSlot w13 (d := sE1) (by decide) fun s14 u14 => ?_
  have w14 := w13.of_upd u14 (by decide) (by decide) (by decide)
  refine wp_ldrSlot w14 (d := sOk) (by decide) fun s15 u15 => ?_
  have w15 := w14.of_upd u15 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s16 u16 => ?_
  have w16 := w15.of_upd u16 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s17 u17 => ?_
  have w17 := w16.of_upd u17 (by decide) (by decide) (by decide)
  -- Memory is unchanged so far.
  have m17 : s17.mem = s.mem := by
    rw [u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem,
      u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have r17 : Rest [.r1, .r2, .r3, .r4, .r5, .r10] s s17 :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
    ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans ((u7.rest (by simp)).trans ((u8.rest (by simp)).trans
    ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans ((u11.rest (by simp)).trans ((u12.rest (by simp)).trans
    ((u13.rest (by simp)).trans ((u14.rest (by simp)).trans ((u15.rest (by simp)).trans ((u16.rest (by simp)).trans
    (u17.rest (by simp)))))))))))))))))
  have h17 := h.of_rest r17 m17 (by decide)
  have hm17 := hm.of_rest r17 m17
  -- The values.
  have rd : ∀ d ∈ LS, s.mem.readW (off (State.addr P.B) d) 32 = BitVec.ofNat 32 (V σ d) := fun d hd => h.readSlot hd
  have a1 : s1.gpr .r1 = BitVec.ofNat 32 (kf σ) := by rw [u1.gpr, rd sK lK, vK]
  have a2 : s2.gpr .r2 = BitVec.ofNat 32 (tf σ) := by rw [u2.gpr, u1.mem, rd sTc lT, vT]
  have a2' : s2.gpr .r1 = BitVec.ofNat 32 (kf σ) := by rw [u2.other _ (by decide), a1]
  have a4 : s4.gpr .r3 = BitVec.ofNat 32 (b2n (decide (kf σ < tf σ))) := by
    rw [u4.gpr, u3.gpr, dpVal, a2', a2, VG.Proof.Rsa.lt_bv (by omega_arith) ht]
  have a5 : s5.gpr .r4 = BitVec.ofNat 32 (b2n (dn σ)) := by
    rw [u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem, rd sDone lD, vD]
  have a7 : s7.gpr .r3 = BitVec.ofNat 32 (b2n (decide (kf σ < tf σ))) &&& (BitVec.ofNat 32 (b2n (dn σ)) ^^^ 1) := by
    rw [u7.gpr, dpVal, u6.other _ (by decide), u5.other _ (by decide), a4, u6.gpr, dpVal, a5]
  have a11 : s11.gpr .r1 = BitVec.ofNat 32 (b2n (decide (kf σ + 1 = tf σ))) := by
    rw [u11.gpr, u10.gpr, dpVal, u9.gpr, dpVal, u8.gpr, dpVal, u8.other .r2 (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), a2', a2, VG.Proof.Rsa.eq1_bv hk ht]
  have a13 : s13.gpr .r1 = BitVec.ofNat 32 (b2n (decide (kf σ + 1 = tf σ))) ||| BitVec.ofNat 32 (b2n (e2 σ)) := by
    rw [u13.gpr, dpVal, u12.other _ (by decide), a11, u12.gpr, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem,
      u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, rd sE2 lE2, vE2]
  have m13 : s13.mem = s.mem := by
    rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have a14 : s14.gpr .r2 = BitVec.ofNat 32 (b2n (e1 σ)) := by rw [u14.gpr, m13, rd sE1 lE1, vE1]
  have a15 : s15.gpr .r5 = BitVec.ofNat 32 (b2n (ok σ)) := by rw [u15.gpr, u14.mem, m13, rd sOk lO, vO]
  have a15' : s15.gpr .r3 = s7.gpr .r3 := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide),
      u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide)]
  have a16 : s16.gpr .r10 = s7.gpr .r3 &&& BitVec.ofNat 32 (b2n (e1 σ)) := by
    rw [u16.gpr, dpVal, a15', u15.other _ (by decide), a14]
  have a17 : s17.gpr .r5 = BitVec.ofNat 32 (b2n (ok σ)) ||| (s7.gpr .r3 &&& BitVec.ofNat 32 (b2n (e1 σ))) := by
    rw [u17.gpr, dpVal, u16.other _ (by decide), a15, a16]
  have f1 : s17.gpr .r1 = s13.gpr .r1 := by
    rw [u17.other _ (by decide), u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide)]
  have f2 : s17.gpr .r2 = s14.gpr .r2 := by
    rw [u17.other _ (by decide), u16.other _ (by decide), u15.other _ (by decide)]
  have f3 : s17.gpr .r3 = s7.gpr .r3 := by rw [u17.other _ (by decide), u16.other _ (by decide), a15']
  have f4 : s17.gpr .r4 = s5.gpr .r4 := by
    rw [u17.other _ (by decide), u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide),
      u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide),
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide)]
  obtain ⟨mo, md, ml⟩ := VG.Proof.Rsa.masks_bv (decide (kf σ < tf σ)) (decide (kf σ + 1 = tf σ)) (dn σ) (ok σ)
    (e1 σ) (e2 σ)
  have tn : ∀ b : Bool, (BitVec.ofNat 32 (b2n b)).toNat = b2n b := fun b => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Rsa.b2n_le b; omega_arith)]
  -- The stores.
  refine h17.strSlot_m hm17 w17 (d := sOk) (r := .r5) (by decide) fun t1 ht1 hmt1 hwt1 g1 _ => ?_
  refine wp_dp (op2_reg _ _) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => ?_
  refine wp_dp (op2_reg _ _) fun t4 v4 => ?_
  have r4 : Rest [.r10, .r4] t1 t4 := (v2.rest (by simp)).trans ((v3.rest (by simp)).trans (v4.rest (by simp)))
  have mt4 : t4.mem = t1.mem := by rw [v4.mem, v3.mem, v2.mem]
  obtain ⟨ht4, hwt4⟩ := ht1.reg hwt1 r4 mt4
  have b3 : t3.gpr .r10 = (BitVec.ofNat 32 (b2n (e1 σ)) |||
      (BitVec.ofNat 32 (b2n (decide (kf σ + 1 = tf σ))) ||| BitVec.ofNat 32 (b2n (e2 σ)))) &&&
      (BitVec.ofNat 32 (b2n (decide (kf σ < tf σ))) &&& (BitVec.ofNat 32 (b2n (dn σ)) ^^^ 1)) := by
    rw [v3.gpr, dpVal, v2.gpr, dpVal, v2.other _ (by decide), g1, f2, f1, f3, a14, a13, a7]
  have b4 : t4.gpr .r4 = BitVec.ofNat 32 (b2n (dn σ)) ||| t3.gpr .r10 := by
    rw [v4.gpr, dpVal, v3.other _ (by decide), v2.other _ (by decide), g1, f4, a5]
  refine ht4.strSlot_m (hmt1.of_rest r4 mt4) hwt4 (d := sDone) (r := .r4) (by decide)
    fun t5 ht5 hmt5 hwt5 g5 _ => ?_
  refine wp_dp (op2_imm (by decide)) fun t6 v6 => ?_
  refine wp_dp (op2_reg _ _) fun t7 v7 => ?_
  have r7 : Rest [.r10] t5 t7 := (v6.rest (by simp)).trans (v7.rest (by simp))
  have mt7 : t7.mem = t5.mem := by rw [v7.mem, v6.mem]
  obtain ⟨ht7, hwt7⟩ := ht5.reg hwt5 r7 mt7
  have b7 : t7.gpr .r10 = (t3.gpr .r10 ^^^ 1) &&&
      (BitVec.ofNat 32 (b2n (decide (kf σ < tf σ))) &&& (BitVec.ofNat 32 (b2n (dn σ)) ^^^ 1)) := by
    rw [v7.gpr, dpVal, v6.gpr, dpVal, v6.other .r3 (by decide), g5, v4.other .r10 (by decide),
      v4.other .r3 (by decide), v3.other .r3 (by decide), v2.other .r3 (by decide), g1, f3, a7]
  refine ht7.strSlot_m (hmt5.of_rest r7 mt7) hwt7 (d := sLive) (r := .r10) (by decide)
    fun t8 ht8 hmt8 hwt8 _ _ => WP.block_nil ⟨e, ?_, hmt8, hwt8⟩
  rw [b7, b3, ml, tn, b4, b3, md, tn, a17, a7, mo, tn] at ht8
  exact ht8

end

end VG.Proof.Rsa.Arm.Recover
