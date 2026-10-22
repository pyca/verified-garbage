module

public import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverFused
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Boolean state operations of the fused pass, preserving its workspace. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Impl.Rsa.Arm.RecoverFused
open VG.Proof.Rsa (b2n)

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat}
  {L LW LS : List Nat}

theorem St.pflagNot {d a : Nat} {x : State → Bool} (cert : Cert (.block (flagNot d a))) (hd : SlotOk d) (ha : a ∈ LS)
    (va : ∀ σ, E σ → V σ a = b2n (x σ)) :
    VP (St P E A L AW LW V LS P.w nArr) (.block (flagNot d a))
      (St P E A L AW LW (fun σ => upd (V σ) d (b2n (!x σ))) (d :: LS) P.w nArr) := by
  refine VP.ctx cert (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  unfold flagNot
  refine h.ldrSlot hw ha (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  obtain ⟨h2, hw2⟩ := h1.reg hw1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have m2 := (hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have value : (s2.gpr .r1).toNat = b2n (!x σ) := by
    rw [u2.gpr, dpVal, u1.gpr, va σ e]
    cases x σ <;> decide
  refine h2.strSlot_m m2 hw2 hd (r := .r1) fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [value] at ht
  exact ht

theorem St.pflagBin (isOr : Bool) {d a b : Nat} {x y : State → Bool}
    (cert : Cert (.block (flagBin isOr d a b)))
    (hd : SlotOk d) (ha : a ∈ LS) (hb : b ∈ LS)
    (va : ∀ σ, E σ → V σ a = b2n (x σ)) (vb : ∀ σ, E σ → V σ b = b2n (y σ)) :
    VP (St P E A L AW LW V LS P.w nArr) (.block (flagBin isOr d a b))
      (St P E A L AW LW (fun σ => upd (V σ) d (b2n (if isOr then x σ || y σ else x σ && y σ)))
        (d :: LS) P.w nArr) := by
  refine VP.ctx cert (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  unfold flagBin
  refine h.ldrSlot hw ha (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine h1.ldrSlot hw1 hb (r := .r2) (by decide) fun s2 h2 hw2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain ⟨h3, hw3⟩ := h2.reg hw2 (u3.rest (ws := [.r1]) (by simp)) u3.mem
  have m3 := ((hm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem).of_rest
    (u2.rest (ws := [.r2]) (by simp)) u2.mem).of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  have value : (s3.gpr .r1).toNat = b2n (if isOr then x σ || y σ else x σ && y σ) := by
    rw [u3.gpr]
    cases isOr <;> simp only [Bool.false_eq_true, ↓reduceIte, dpVal]
      <;> rw [u2.other _ (by decide), u1.gpr, u2.gpr, va σ e, vb σ e]
      <;> cases x σ <;> cases y σ <;> decide
  refine h3.strSlot_m m3 hw3 hd (r := .r1) fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [value] at ht
  exact ht

end
end VG.Proof.Rsa.Arm.Recover
