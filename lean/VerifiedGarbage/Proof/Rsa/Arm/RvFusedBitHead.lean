module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedFlags
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt

/-! Read the next exponent bit and advance its byte without secret branches. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverFused

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.pfusedBitHead (hb : sByte ∈ LS) (bound : ∀ σ, E σ → V σ sByte < 256) :
    VP (St P E A L AW LW V LS P.w nArr) (.block bitHead)
      (St P E A L AW LW (fun σ => upd (upd (V σ) sBit (V σ sByte / 128 % 2))
        sByte (2 * V σ sByte % 256)) (sByte :: sBit :: LS) P.w nArr) := by
  refine VP.ctx ⟨_, by taint_decide⟩ (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  have small := bound σ e
  unfold bitHead
  refine h.ldrSlot hw hb (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  have m1 := hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hw2⟩ := h1.reg hw1 (u2.rest (ws := [.r2]) (by simp)) u2.mem
  have m2 := m1.of_rest (u2.rest (ws := [.r2]) (by simp)) u2.mem
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain ⟨h3, hw3⟩ := h2.reg hw2 (u3.rest (ws := [.r2]) (by simp)) u3.mem
  have m3 := m2.of_rest (u3.rest (ws := [.r2]) (by simp)) u3.mem
  have value : (s3.gpr .r2).toNat = V σ sByte / 128 % 2 := by
    rw [u3.gpr, dpVal, bv_and_one, u2.gpr, BitVec.toNat_ushiftRight, u1.gpr,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show V σ sByte < 2 ^ 32 by omega)]
    rw [Nat.shiftRight_eq_div_pow]
  refine h3.strSlot_m m3 hw3 (d := sBit) (r := .r2) (by decide) fun s4 h4 m4 hw4 g4 _ => ?_
  rw [value] at h4
  refine wp_mov (op2_lsl (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hw5⟩ := h4.reg hw4 (u5.rest (ws := [.r1]) (by simp)) u5.mem
  have m5 := m4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  obtain ⟨h6, hw6⟩ := h5.reg hw5 (u6.rest (ws := [.r1]) (by simp)) u6.mem
  have m6 := m5.of_rest (u6.rest (ws := [.r1]) (by simp)) u6.mem
  have next : (s6.gpr .r1).toNat = 2 * V σ sByte % 256 := by
    rw [u6.gpr, dpVal, u5.gpr, g4, u3.other _ (by decide), u2.other _ (by decide), u1.gpr,
      BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show V σ sByte < 2 ^ 32 by omega), Nat.shiftLeft_eq]
    change ((V σ sByte * 2) % 4294967296) &&& (2 ^ 8 - 1) = 2 * V σ sByte % 256
    rw [Nat.mod_eq_of_lt (show V σ sByte * 2 < 4294967296 by omega),
      Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm]
  refine h6.strSlot_m m6 hw6 (d := sByte) (r := .r1) (by decide)
    fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [next] at ht
  exact ht

end
end VG.Proof.Rsa.Arm.Recover
