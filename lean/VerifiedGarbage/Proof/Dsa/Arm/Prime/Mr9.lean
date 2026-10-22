module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont1
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mr2
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Taint7
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads

/-! # A candidate on ARMv7: a witness that passed (`St.ponPass`)

`i += 1`, `uniform +=` the witness's flag, and `sStat := 4` if more
witnesses are needed (`i ≤ 16` or `uniform < checks`), else 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)

theorem b2n_or32 (x y : Bool) :
    BitVec.ofNat 32 (b2n x) ||| BitVec.ofNat 32 (b2n y) = BitVec.ofNat 32 (b2n (x || y)) := by
  cases x <;> cases y <;> decide

theorem tri_b2n (g : Bool) :
    BitVec.ofNat 32 (b2n g) + (BitVec.ofNat 32 (b2n g) <<< 1) + 1 = BitVec.ofNat 32 (if g then 4 else 1) := by
  cases g <;> decide

theorem lt_bit' {x k : Nat} (hx : x < 2 ^ 31) (hk : k < 2 ^ 31) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 k) >>> 31 = BitVec.ofNat 32 (b2n (decide (x < k))) := by
  apply BitVec.eq_of_toNat_eq
  rw [lt_bit hx hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := VG.Proof.Rsa.b2n_le (decide (x < k)); omega)]

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `onPass`: `i += 1`, `uniform +=` the flag `sU`, and `sStat := 4` if more
witnesses are needed, else 1. -/
theorem St.ponPass (hI : sI ∈ LS) (hUni : sUni ∈ LS) (hU : sU ∈ LS) (hChk : sChk ∈ LS)
    (hv : ∀ σ, E σ → V σ sI < 2 ^ 30 ∧ V σ sUni < 2 ^ 30 ∧ V σ sU ≤ 1 ∧ V σ sChk < 2 ^ 30) :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block onPass)
      (fun σ s => St P E A L (fun σ => upd (upd (upd (V σ) sI (V σ sI + 1)) sUni (V σ sUni + V σ sU)) sStat
        (if (decide (V σ sI + 1 < 17) || decide (V σ sUni + V σ sU < V σ sChk)) then 4 else 1))
        (sStat :: sUni :: sI :: LS) σ s ∧ MS P σ s) :=
  VP.kv onPass_taint (fun _ _ h => h.1.2.2) fun σ s ⟨⟨e, h, hw⟩, m⟩ => by
    obtain ⟨bI, bUni, bU, bChk⟩ := hv σ e
    simp only [onPass, goFlag, List.cons_append, List.nil_append]
    refine h.ldrM m hw hI (r := .r1) (by decide) fun s1 h1 hw1 m1 u1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    have v2 : (s2.gpr .r1).toNat = V σ sI + 1 := by
      rw [u2.gpr, dpVal, u1.gpr, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    refine (h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem).strM (m1.of_upd u2)
      (hw1.of_upd u2 (by decide) (by decide) (by decide)) (d := sI) (by decide) fun s3 h3 hw3 m3 _ => ?_
    rw [v2] at h3
    refine h3.ldrM m3 hw3 (d := sU) (List.mem_cons_of_mem _ hU) (r := .r2) (by decide) fun s4 h4 hw4 m4 u4 => ?_
    refine h4.ldrM m4 hw4 (d := sUni) (List.mem_cons_of_mem _ hUni) (r := .r3) (by decide)
      fun s5 h5 hw5 m5 u5 => ?_
    refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
    have eU : upd (V σ) sI (V σ sI + 1) sU = V σ sU := upd_ne _ _ (by decide)
    have eUni : upd (V σ) sI (V σ sI + 1) sUni = V σ sUni := upd_ne _ _ (by decide)
    have v6 : (s6.gpr .r3).toNat = V σ sUni + V σ sU := by
      rw [u6.gpr, dpVal, u5.gpr, u5.other _ (by decide), u4.gpr, eU, eUni, BitVec.toNat_add, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat]
      omega
    refine (h5.of_rest (u6.rest (ws := [.r3]) (by simp)) u6.mem).strM (m5.of_upd u6)
      (hw5.of_upd u6 (by decide) (by decide) (by decide)) (d := sUni) (by decide) fun s7 h7 hw7 m7 _ => ?_
    rw [v6] at h7
    have e7I : upd (upd (V σ) sI (V σ sI + 1)) sUni (V σ sUni + V σ sU) sI = V σ sI + 1 := by
      rw [upd_ne _ _ (by decide), upd_self]
    have e7U : upd (upd (V σ) sI (V σ sI + 1)) sUni (V σ sUni + V σ sU) sUni = V σ sUni + V σ sU := upd_self _ _ _
    have e7C : upd (upd (V σ) sI (V σ sI + 1)) sUni (V σ sUni + V σ sU) sChk = V σ sChk := by
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
    refine h7.ldrM m7 hw7 (d := sI) (by simp) (r := .r1) (by decide) fun s8 h8 hw8 m8 u8 => ?_
    refine wp_dp (op2_imm (by decide)) fun s9 u9 => wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
    have r10 : Rest [.r1] s8 s10 := (u9.rest (by simp)).trans (u10.rest (by simp))
    have m10 : s10.mem = s8.mem := by rw [u10.mem, u9.mem]
    refine (h8.of_rest r10 m10).ldrM (m8.of_rest r10 m10) (hw8.rest r10) (d := sUni) (by simp) (r := .r2) (by decide)
      fun s11 h11 hw11 m11 u11 => ?_
    refine h11.ldrM m11 hw11 (d := sChk) (by simp [hChk]) (r := .r3) (by decide) fun s12 h12 hw12 m12 u12 => ?_
    refine wp_dp (op2_reg _ _) fun s13 u13 => wp_mov (op2_lsr (by decide)) fun s14 u14 =>
      wp_dp (op2_reg _ _) fun s15 u15 => wp_dp (op2_lsl (by decide)) fun s16 u16 =>
        wp_dp (op2_imm (by decide)) fun s17 u17 => ?_
    have x10 : s10.gpr .r1 = BitVec.ofNat 32 (b2n (decide (V σ sI + 1 < 17))) := by
      rw [u10.gpr, u9.gpr, dpVal, u8.gpr, e7I, show (17 : BitVec 32) = BitVec.ofNat 32 17 from rfl]
      exact lt_bit' (by omega) (by decide)
    have x14 : s14.gpr .r2 = BitVec.ofNat 32 (b2n (decide (V σ sUni + V σ sU < V σ sChk))) := by
      rw [u14.gpr, u13.gpr, dpVal, u12.other _ (by decide), u11.gpr, u12.gpr, e7U, e7C]
      exact lt_bit' (by omega) (by omega)
    have x14' : s14.gpr .r1 = s10.gpr .r1 := by
      rw [u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide)]
    have x17 : s17.gpr .r1 = BitVec.ofNat 32
        (if (decide (V σ sI + 1 < 17) || decide (V σ sUni + V σ sU < V σ sChk)) then 4 else 1) := by
      rw [u17.gpr, dpVal, u16.gpr, dpVal, u15.gpr, dpVal, x14', x10, x14, b2n_or32]
      exact tri_b2n _
    have r17 : Rest [.r1, .r2, .r3] s12 s17 := (u13.rest (by simp)).trans ((u14.rest (by simp)).trans
      ((u15.rest (by simp)).trans ((u16.rest (by simp)).trans (u17.rest (by simp)))))
    have m17 : s17.mem = s12.mem := by rw [u17.mem, u16.mem, u15.mem, u14.mem, u13.mem]
    clear u17 u16 u15 u14 u13
    refine (h12.of_rest r17 m17).strM (m12.of_rest r17 m17) (hw12.rest r17) (d := sStat) (by decide)
      fun t ht hwt mt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, mt⟩
    have v17 : (BitVec.ofNat 32 (if (decide (V σ sI + 1 < 17) || decide (V σ sUni + V σ sU < V σ sChk)) then 4
        else 1)).toNat = if (decide (V σ sI + 1 < 17) || decide (V σ sUni + V σ sU < V σ sChk)) then 4 else 1 := by
      split <;> rfl
    rw [x17, v17] at ht
    exact ht

end

end VG.Proof.Dsa.Arm.Prime
