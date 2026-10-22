module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedState
import VerifiedGarbage.Proof.Rsa.Arm.RvSt2
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
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

/-! Initialize a descending byte pointer and its public loop length. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverFused

def byteInitV (P : RP) (V : Nat → Nat) : Nat → Nat :=
  upd (upd V sBytes (P.el + P.dl)) sPtr (P.B.toNat + arr P.W wM + (P.el + P.dl) - 1)

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.pfusedByteInit :
    VP (St P E A L AW LW V LS P.w nArr) (.block byteInit)
      (St P E A L AW LW (fun σ => byteInitV P (V σ)) (sPtr :: sBytes :: LS) P.w nArr) := by
  simp only [byteInit, List.append_assoc]
  refine VP.block_append St.pctxW (VP.block_append St.pldrLens (VP.block_append ?_ St.pctxw))
  refine VP.ctx ⟨_, by taint_decide⟩ (fun _ _ h => h.1.2.2.2)
    fun σ s ⟨⟨e, h, mm, hw⟩, r1, r2⟩ => ?_
  have pre := h.bs.pre
  have lengths : P.el + P.dl ≤ 2 * P.K := by have := pre.el2; have := pre.dl2; omega
  have positive : 0 < P.el + P.dl := by have := pre.el1; omega
  have kw := pre.sizes.kw
  have wpos : 2 ≤ P.w := by simp only [RP.w]; omega
  have words : P.W = 2 * P.w + 2 := rfl
  have fits := fitZ_W pre.sizes (show wM < 22 by decide)
  have stride : S P.W = 4 * (P.W + 2) := rfl
  have nowrap := hw.nowrap
  have arrPos : 0 < arr P.W wM := by simp only [arr, hdr]; omega
  unfold byteInitTail
  refine ptr_ok hw (r := .r0) (by decide) (j := wM) (by decide) fun s1 p1 rest1 mem1 hw1 => ?_
  have h1 := h.of_rest rest1 mem1 (by decide)
  have mm1 := mm.of_rest rest1 mem1
  have lens1 : s1.gpr .r1 = BitVec.ofNat 32 P.el := (rest1.gpr _ (by decide)).trans r1
  have lens2 : s1.gpr .r2 = BitVec.ofNat 32 P.dl := (rest1.gpr _ (by decide)).trans r2
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain ⟨h2, hw2⟩ := h1.reg hw1 (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have mm2 := mm1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  have count : s2.gpr .r1 = BitVec.ofNat 32 (P.el + P.dl) := by
    rw [u2.gpr, dpVal, lens1, lens2, BitVec.ofNat_add_ofNat]
  have p2 : s2.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W wM) := (u2.other _ (by decide)).trans p1
  refine h2.strSlot_m mm2 hw2 (d := sBytes) (r := .r1) (by decide) fun s3 h3 mm3 hw3 g3 _ => ?_
  rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show P.el + P.dl < 2 ^ 32 by
    have := pre.k2; omega)] at h3
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  obtain ⟨h4, hw4⟩ := h3.reg hw3 (u4.rest (ws := [.r0]) (by simp)) u4.mem
  have mm4 := mm3.of_rest (u4.rest (ws := [.r0]) (by simp)) u4.mem
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  obtain ⟨h5, hw5⟩ := h4.reg hw4 (u5.rest (ws := [.r0]) (by simp)) u5.mem
  have mm5 := mm4.of_rest (u5.rest (ws := [.r0]) (by simp)) u5.mem
  have pointer : (s5.gpr .r0).toNat = P.B.toNat + arr P.W wM + (P.el + P.dl) - 1 := by
    rw [u5.gpr, dpVal, u4.gpr, dpVal, g3, p2, count]
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine h5.strSlot_m mm5 hw5 (d := sPtr) (r := .r0) (by decide)
    fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
  rw [pointer] at ht
  exact ht

end
end VG.Proof.Rsa.Arm.Recover
