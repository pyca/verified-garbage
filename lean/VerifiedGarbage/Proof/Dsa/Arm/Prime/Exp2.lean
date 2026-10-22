module
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.St

import VerifiedGarbage.Proof.Dsa.Arm.Prime.Instr
import VerifiedGarbage.Proof.Rsa.Arm.RvHalving
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Loads

/-! # A candidate on ARMv7: the halvings (`halving_vp`)

A halving (`halfBody_vp`): `m / 2` into `aH2`, `m` even into `sBit` and
`t +=` it, `m` selected, and the count decremented.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n halveStep)
open VG.Impl.RsaKeyGen.Arm.Key (notS)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `sBit := 1 − sBit` and `sTc +=` it. -/
theorem St.pnotAdd (cert : Cert (.block (notS sBit sBit ++ ([.ldr .r2 .r8 sTc, .dp .add .r2 .r2 (.reg .r1),
      .str .r2 .r8 sTc] : List Instr))))
    (hb : sBit ∈ LS) (ht : sTc ∈ LS) (bit : ∀ σ, E σ → V σ sBit ≤ 1) (lt : ∀ σ, E σ → V σ sTc + 1 < 2 ^ 32) :
    VP (St P E A L V LS) (.block (notS sBit sBit ++ ([.ldr .r2 .r8 sTc, .dp .add .r2 .r2 (.reg .r1),
      .str .r2 .r8 sTc] : List Instr)))
      (St P E A L (fun σ => upd (upd (V σ) sBit (1 - V σ sBit)) sTc (V σ sTc + (1 - V σ sBit)))
        (sTc :: sBit :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    have b := bit σ e
    have l := lt σ e
    simp only [notS, List.cons_append, List.nil_append]
    refine h.ldr hw hb (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
    have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
    have hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
    have v2 : s2.gpr .r1 = BitVec.ofNat 32 (1 - V σ sBit) := by
      rw [u2.gpr, dpVal, u1.gpr]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_xor, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
      rcases (by omega : V σ sBit = 0 ∨ V σ sBit = 1) with h0 | h0 <;> rw [h0] <;> decide
    refine h2.str hw2 (d := sBit) (by decide) fun s3 h3 hw3 m3 => ?_
    rw [v2, ofNat_toNat_lt (by omega)] at h3
    refine h3.ldr hw3 (List.mem_cons_of_mem _ ht) (r := .r2) (by decide) fun s4 h4 hw4 u4 => ?_
    refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
    have h5 := h4.of_rest (u5.rest (ws := [.r2]) (by simp)) u5.mem
    have hw5 := hw4.of_upd u5 (by decide) (by decide) (by decide)
    refine h5.str hw5 (d := sTc) (by decide) fun t ht' hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
    have v5 : (s5.gpr .r2).toNat = V σ sTc + (1 - V σ sBit) := by
      rw [u5.gpr, dpVal, u4.gpr, u4.other _ (by decide), m3.gpr, v2, upd_ne _ _ (by decide),
        BitVec.toNat_add, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
      omega
    rw [v5] at ht'
    exact ht'

/-- The count decremented, with Z iff it reaches 0. -/
theorem St.pcntNext (cert : Cert (.block cntNext)) (hc : sCnt ∈ LS)
    (pos : ∀ σ, E σ → 1 ≤ V σ sCnt ∧ V σ sCnt < 2 ^ 32) :
    VP (St P E A L V LS) (.block cntNext)
      (fun σ s => St P E A L (fun σ => upd (V σ) sCnt (V σ sCnt - 1)) (sCnt :: LS) σ s ∧
        s.z = decide (V σ sCnt - 1 = 0)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => by
    have p := pos σ e
    simp only [cntNext]
    refine h.ldr hw hc (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
    refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
    have h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
    have hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
    have v2 : s2.gpr .r1 = BitVec.ofNat 32 (V σ sCnt - 1) := by
      rw [u2.gpr, u1.gpr]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
      simp only [show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    refine h2.strz hw2 (d := sCnt) (by decide) fun t ht hwt zt => WP.block_nil ⟨⟨e, ?_, hwt⟩, ?_⟩
    · rwa [v2, ofNat_toNat_lt (by omega)] at ht
    · rw [zt, z2, ← u2.gpr, v2]
      by_cases h0 : V σ sCnt - 1 = 0
      · simp [h0]
      · have : BitVec.ofNat 32 (V σ sCnt - 1) ≠ 0 := fun e' => h0 (by
          have := congrArg BitVec.toNat e'; rw [ofNat_toNat_lt (by omega)] at this; simpa using this)
        simpa [h0] using this

end

end VG.Proof.Dsa.Arm.Prime
