module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedState
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.RecoverFused

/-! Initialize header words without reading uninitialized scratch memory. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverFused

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.pconstant {d v : Nat} (hd : SlotOk d) (bound : v < 2 ^ 32)
    (enc : encodable (BitVec.ofNat 32 v) = true) (cert : Cert (.block (constant d v))) :
    VP (St P E A L AW LW V LS P.w nArr) (.block (constant d v))
      (St P E A L AW LW (fun σ => upd (V σ) d v) (d :: LS) P.w nArr) := by
  refine VP.ctx cert (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, mm, hw⟩ => ?_
  unfold constant
  refine wp_mov (op2_imm enc) fun s1 u1 => ?_
  obtain ⟨h1, hw1⟩ := h.reg hw (u1.rest (ws := [.r1]) (by simp)) u1.mem
  have mm1 := mm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine h1.strSlot_m mm1 hw1 hd (r := .r1)
    fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at ht
  exact ht

end
end VG.Proof.Rsa.Arm.Recover
