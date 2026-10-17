module

public import VerifiedGarbage.Proof.Rsa.Arm.RvSq2
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: from `y = g^r` to the squarings, and the next candidate

`sqStart_vp`: `y = ±1` and the start of the squarings; `St.pcandNext`: the
count of candidates and whether to go on.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n sqIter sqStep sqStart)

theorem b2n_or (a b : Bool) :
    BitVec.ofNat 32 (b2n a) ||| BitVec.ofNat 32 (b2n b) = BitVec.ofNat 32 (b2n (a || b)) := by
  cases a <;> cases b <;> decide

section
variable {P : RP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {AW : State → Nat → Nat}
  {LW : List Nat} {V : State → Nat → Nat} {LS : List Nat}

/-- `done := (y = 1) ∨ (y = -1)`, `ok := 0`, `k := 0`. -/
theorem St.psqHead {e1 e2 : State → Bool} (h1 : sE1 ∈ LS) (h2 : sE2 ∈ LS)
    (hv : ∀ σ, E σ → V σ sE1 = b2n (e1 σ) ∧ V σ sE2 = b2n (e2 σ)) :
    VP (St P E A L AW LW V LS P.w nArr) (.block sqHead)
      (St P E A L AW LW (fun σ => upd (upd (upd (V σ) sDone (b2n (e1 σ || e2 σ))) sOk 0) sK 0)
        (sK :: sOk :: sDone :: LS) P.w nArr) := by
  refine VP.ctx sqHead_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  obtain ⟨v1, v2⟩ := hv σ e
  refine h.ldrSlot hw h1 (r := .r1) (by decide) fun s1 g1 hw1 u1 => ?_
  have m1 := hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine g1.ldrSlot hw1 h2 (r := .r2) (by decide) fun s2 g2 hw2 u2 => ?_
  have m2 := m1.of_rest (u2.rest (ws := [.r2]) (by simp)) u2.mem
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨g3, hw3⟩ := g2.reg hw2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  have m3 := m2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  have e3 : (s3.gpr .r1).toNat = b2n (e1 σ || e2 σ) := by
    rw [u3.gpr, dpVal, u2.other _ (by decide), u1.gpr, u2.gpr, v1, v2, b2n_or, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := VG.Proof.Rsa.b2n_le (e1 σ || e2 σ); omega)]
  refine g3.strSlot_m m3 hw3 (d := sDone) (r := .r1) (by decide) fun s4 g4 m4 hw4 _ _ => ?_
  rw [e3] at g4
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  obtain ⟨g5, hw5⟩ := g4.reg hw4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
  have m5 := m4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine g5.strSlot_m m5 hw5 (d := sOk) (r := .r1) (by decide) fun s6 g6 m6 hw6 gp6 _ => ?_
  refine g6.strSlot_m m6 hw6 (d := sK) (r := .r1) (by decide) fun t gt mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [gp6, u5.gpr] at gt
  exact gt

/-- The candidates tried `+= 1`; Z unless fewer than 100 are tried and none gave the factors. -/
theorem St.pcandNext {okb : State → Bool} (hc : sCand ∈ LS) (ho : sOk ∈ LS)
    (hv : ∀ σ, E σ → V σ sCand < 100 ∧ V σ sOk = b2n (okb σ)) :
    VP (St P E A L AW LW V LS P.w nArr) (.block candNext) (fun σ s =>
      St P E A L AW LW (fun σ => upd (V σ) sCand (V σ sCand + 1)) (sCand :: LS) P.w nArr σ s ∧
        s.z = !(decide (V σ sCand + 1 < 100) && !okb σ)) := by
  refine VP.ctx candNext_taint (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  obtain ⟨v1, v2⟩ := hv σ e
  unfold candNext
  refine h.ldrSlot hw hc (r := .r1) (by decide) fun s1 g1 hw1 u1 => ?_
  have m1 := hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨g2, hw2⟩ := g1.reg hw1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have m2 := m1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have e2 : s2.gpr .r1 = BitVec.ofNat 32 (V σ sCand + 1) := by
    rw [u2.gpr, dpVal, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  refine g2.strSlot_m m2 hw2 (d := sCand) (r := .r1) (by decide) fun s3 g3 m3 hw3 gp3 _ => ?_
  rw [e2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at g3
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have hS : Rest [.r1] s3 s5 := (u4.rest (by simp)).trans (u5.rest (by simp))
  obtain ⟨g5, hw5⟩ := g3.reg hw3 hS (u5.mem.trans u4.mem)
  have m5 := m3.of_rest hS (u5.mem.trans u4.mem)
  have e5 : s5.gpr .r1 = BitVec.ofNat 32 (b2n (decide (V σ sCand + 1 < 100))) := by
    rw [u5.gpr, u4.gpr, dpVal, gp3, e2, show (100 : BitVec 32) = BitVec.ofNat 32 100 from rfl,
      VG.Proof.Rsa.lt_bv (by omega) (by decide)]
  refine g5.ldrSlot hw5 (List.mem_cons_of_mem _ ho) (r := .r2) (by decide) fun s6 g6 hw6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u9 z9 => WP.block_nil ⟨⟨e, ?_, ?_, ?_⟩, ?_⟩
  · have r : Rest [.r1, .r2] s6 t := (u7.rest (by simp)).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))
    exact (g6.reg hw6 r (by rw [u9.mem, u8.mem, u7.mem])).1
  · have r : Rest [.r1, .r2] s5 t := (u6.rest (by simp)).trans ((u7.rest (by simp)).trans
      ((u8.rest (by simp)).trans (u9.rest (by simp))))
    exact m5.of_rest r (by rw [u9.mem, u8.mem, u7.mem, u6.mem])
  · exact ((((hw6.of_upd u7 (by decide) (by decide) (by decide)).of_upd u8 (by decide) (by decide)
      (by decide)).of_upd u9 (by decide) (by decide) (by decide)))
  · have e8 : s8.gpr .r1 = BitVec.ofNat 32 (b2n (decide (V σ sCand + 1 < 100) && !okb σ)) := by
      rw [u8.gpr, dpVal, u7.other _ (by decide), u6.other _ (by decide), e5, u7.gpr, dpVal, u6.gpr]
      rw [upd_ne _ _ (show sOk ≠ sCand by decide), v2]
      cases decide (V σ sCand + 1 < 100) <;> cases okb σ <;> decide
    rw [z9, e8]
    cases decide (V σ sCand + 1 < 100) <;> cases okb σ <;> decide

end

section
variable {P : RP}

theorem gR_y0 (σ : State) (j : Nat) (h : rv P σ < 2 ^ P.c) :
    gR P j (rv P σ % 2 ^ P.c) = y0 P σ j * Rm P % P.n := by
  rw [Nat.mod_eq_of_lt h, gR, y0, VG.Proof.Bignum.powMod_eq, Nat.mod_mul_mod]

/-- `y = 1`, `y = -1`, and the start of the squarings. -/
theorem sqStart_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) {E : State → Prop} {j : Nat}
    (hr : ∀ σ, E σ → rv P σ < 2 ^ P.c) {R : Prog isa} {G : State → State → Prop} (hR : VP (Qs P E j 0) R G) :
    VP (Xs P E j P.c) (.seq (eqAt sE1 mY aO) (.seq (eqAt sE2 mY aNg) (.seq (.block sqInit) R))) G := by
  have hn0 : 0 < P.n := by omega
  have hR' : Nat.Coprime (Rm P) P.n := VG.Proof.Bignum.coprime_pow2 hn.1 _
  refine VP.seq (St.peqS eqY1_taint (d := sE1) (a := mY) (b := aO) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.peqS eqY2_taint (d := sE2) (a := mY) (b := aNg) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) ?_
  rw [sqInit_eq, cntBits_eq]
  refine VP.seq (VP.block_append (St.psqHead (e1 := fun σ => decide (y0 P σ j = 1))
    (e2 := fun σ => decide (y0 P σ j = P.n - 1)) (by decide) (by decide) fun σ e => ?_)
    ((VP.block_append St.pldrLens St.pcntTail).mono (fun _ _ h => h) fun σ s h => St.mono h ?_ ?_ ?_)) hR
  · have ex : y0 P σ j < P.n := by rw [y0, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hn0
    have eY : Ae P σ j P.c mY = y0 P σ j * Rm P % P.n := by
      rw [← gR_y0 σ j (hr σ e)]; simp [Ae, upd, mY, mG]
    have eO : Ae P σ j P.c aO = Ov P := by simp [Ae, AM, upd, mY, mG, aO, aNg]
    have eN : Ae P σ j P.c aNg = P.n - Ov P := by simp [Ae, AM, upd, mY, mG, aNg]
    rw [eY, eO, eN]
    have i1 := VG.Proof.Rsa.eq_one_mont hR' hn.2 ex (X := y0 P σ j * Rm P % P.n) rfl
    have i2 := VG.Proof.Rsa.eq_neg_mont hR' hn.2 ex (X := y0 P σ j * Rm P % P.n) rfl
    simp only [upd_self, upd_ne _ _ (show sE1 ≠ sE2 by decide)]
    simp only [show (y0 P σ j * Rm P % P.n = Ov P) ↔ y0 P σ j = 1 from i1,
      show (y0 P σ j * Rm P % P.n = P.n - Ov P) ↔ y0 P σ j = P.n - 1 from i2]
    constructor
    · by_cases h : y0 P σ j = 1 <;> simp only [h, b2n, decide_true, decide_false, ite_true, ite_false,
        Bool.false_eq_true]
    · by_cases h : y0 P σ j = P.n - 1 <;> simp only [h, b2n, decide_true, decide_false, ite_true, ite_false,
        Bool.false_eq_true]
  · intro x hx
    refine ⟨by simp only [Lq, Le, liveM, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega, ?_⟩
    simp only [Lq, liveM, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have e1 : Ae P σ j P.c mY = y0 P σ j * Rm P % P.n := by
        rw [← gR_y0 σ j (hr σ h.1)]; simp [Ae, upd, mY, mG]
      rw [e1]; simp only [Aq, upd_self, sqst, sqIter, sqStart]
    all_goals simp [Ae, Aq, upd, mY, mG, aNg, aO, mR2, aOne, aZ, aN]
  · intro x hx
    simp only [List.mem_singleton] at hx; subst hx
    exact ⟨by decide, by simp [AWe, AWh, upd, wR, wRc]⟩
  · intro d hd
    refine ⟨by simp only [LSq, LSe, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; omega, ?_⟩
    simp only [LSq, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upd, Vq, Vc, sqst, sqIter, sqStart, b2n, sOk, sDone, sK, sCnt, sCand, sTc, sE1, sE2]

end

end VG.Proof.Rsa.Arm.Recover
