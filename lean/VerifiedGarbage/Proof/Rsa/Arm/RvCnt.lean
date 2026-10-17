module

public import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the loops' count (`cntNext_ok`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- `cntNext`: the count in `sCnt` decremented, Z when it reaches 0. -/
theorem KS.cntNext_ok {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (hc : sCnt ∈ ls) (h1 : 1 ≤ V sCnt) (h2 : V sCnt < 2 ^ 32) :
    WP isa (.block cntNext) s fun t => KS P σ A live AW liveW (upd V sCnt (V sCnt - 1)) (sCnt :: ls) t ∧
      Ws t P.B P.Z v N ∧ t.z = decide (V sCnt - 1 = 0) := by
  unfold VG.Impl.Rsa.Arm.Recover.cntNext
  refine h.ldrSlot hv hc (r := .r1) (by decide) fun s1 h1' hv1 u1 => ?_
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  obtain ⟨h2', hv2⟩ := h1'.reg hv1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  refine h2'.strSlot hv2 (d := sCnt) (r := .r1) (by decide) fun t ht hvt gt zt => WP.block_nil ⟨?_, hvt, ?_⟩
  · have e : (s2.gpr .r1).toNat = V sCnt - 1 := by
      rw [u2.gpr, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e] at ht; exact ht
  · rw [zt, z2, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    rfl

end

end VG.Proof.Rsa.Arm.Recover
