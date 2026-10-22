module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedState
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.RecoverFused

/-! Public byte pointers and loop counts, with their zero flags. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverFused

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.pdecrement {d : Nat} (hd : d ∈ LS) (cert : Cert (.block (decrement d)))
    (bound : ∀ σ, E σ → 1 ≤ V σ d ∧ V σ d < 2 ^ 32) :
    VP (St P E A L AW LW V LS P.w nArr) (.block (decrement d))
      (fun σ s => St P E A L AW LW (fun σ => upd (V σ) d (V σ d - 1)) (d :: LS) P.w nArr σ s ∧
        s.z = decide (V σ d - 1 = 0)) := by
  refine VP.ctx cert (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, mm, hw⟩ => ?_
  obtain ⟨lo, hi⟩ := bound σ e
  unfold decrement
  refine h.ldrSlot hw hd (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  have mm1 := mm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  obtain ⟨h2, hw2⟩ := h1.reg hw1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have mm2 := mm1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have word : s1.gpr .r1 - 1 = BitVec.ofNat 32 (V σ d - 1) := by
    rw [u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) lo]
  refine h2.strSlot_m mm2 hw2 (h.ls_ok d hd) (r := .r1)
    fun t ht mt hwt _ zt => WP.block_nil ⟨⟨e, ?_, mt, hwt⟩, ?_⟩
  · rw [u2.gpr, word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    exact ht
  · rw [zt, z2, word, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
      ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl

def byteTailV (V : Nat → Nat) : Nat → Nat :=
  upd (upd V sPtr (V sPtr - 1)) sBytes (V sBytes - 1)

theorem St.pfusedByteTail (hp : sPtr ∈ LS) (hc : sBytes ∈ LS)
    (ptr : ∀ σ, E σ → 1 ≤ V σ sPtr ∧ V σ sPtr < 2 ^ 32)
    (count : ∀ σ, E σ → 1 ≤ V σ sBytes ∧ V σ sBytes < 2 ^ 32) :
    VP (St P E A L AW LW V LS P.w nArr) (.block byteTail)
      (fun σ s => St P E A L AW LW (fun σ => byteTailV (V σ)) (sBytes :: sPtr :: LS) P.w nArr σ s ∧
        s.z = decide (V σ sBytes - 1 = 0)) := by
  unfold byteTail
  refine VP.block_append ((St.pdecrement hp ⟨_, by taint_decide⟩ ptr).mono
    (fun _ _ h => h) (fun _ _ h => h.1)) ?_
  refine (St.pdecrement (d := sBytes) (by simp only [List.mem_cons]; right; exact hc)
    ⟨_, by taint_decide⟩ (fun σ e => ?_)).mono (fun _ _ h => h) fun σ s h => ?_
  · simpa only [upd_ne _ _ (show sBytes ≠ sPtr by decide)] using count σ e
  · simpa only [byteTailV, upd_ne _ _ (show sBytes ≠ sPtr by decide)] using h

end
end VG.Proof.Rsa.Arm.Recover
