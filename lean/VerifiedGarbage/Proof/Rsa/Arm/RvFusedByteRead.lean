module

import VerifiedGarbage.Proof.Rsa.Arm.RvFusedState
import VerifiedGarbage.Proof.Rsa.Arm.RvSlots
import VerifiedGarbage.Proof.Rsa.Arm.RvKM
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
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

/-! Read an exponent byte at a public address from the preserved wide array. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverFused

theorem num_byte (m : Mem) (B : BitVec 32) (w j i : Nat) (hi : i < 4 * w) :
    (m (off (State.addr B) (arr w j) + BitVec.ofNat 64 i)).toNat =
      num m B w j / 2 ^ (8 * i) % 256 := by
  rw [← Mem.extractLsb'_read m _ hi, BitVec.extractLsb'_toNat,
    VG.Proof.Bignum.read_eq_val32, Nat.shiftRight_eq_div_pow]

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

theorem St.pfusedByteRead {i : Nat} (hi : i < 4 * P.W) (hm : wM ∈ LW) (hp : sPtr ∈ LS)
    (ptr : ∀ σ, E σ → V σ sPtr = P.B.toNat + arr P.W wM + i) :
    VP (St P E A L AW LW V LS P.w nArr) (.block byteHead)
      (St P E A L AW LW (fun σ => upd (V σ) sByte (AW σ wM / 2 ^ (8 * i) % 256))
        (sByte :: LS) P.w nArr) := by
  change VP _ (.block ([.ldr .r0 .r8 sPtr] ++ [.ldrb .r1 .r0 0, .str .r1 .r8 sByte])) _
  refine VP.block_append (G := fun σ s => St P E A L AW LW V LS P.w nArr σ s ∧
    s.gpr .r0 = BitVec.ofNat 32 (P.B.toNat + arr P.W wM + i)) ?_ ?_
  · refine VP.ctx ⟨_, by taint_decide⟩ (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, mm, hw⟩ => ?_
    refine h.ldrSlot hw hp (r := .r0) (by decide) fun t ht hwt u => WP.block_nil
      ⟨⟨e, ht, mm.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, hwt⟩, ?_⟩
    rw [u.gpr, ptr σ e]
  · refine VP.taint [.r0, .r8] ⟨_, by taint_decide⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_)
      fun σ s ⟨⟨e, h, mm, hw⟩, r0⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2, h₂.2]
      · rw [h₁.1.2.1.r8, h₂.1.2.1.r8]
    · have fit := fitZ_W h.sizes (show wM < 22 by decide)
      have nowrap := hw.nowrap
      have step : S P.W = 4 * (P.W + 2) := rfl
      have address : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) =
          off (State.addr P.B) (arr P.W wM) + BitVec.ofNat 64 i := by
        rw [r0]
        apply BitVec.eq_of_toNat_eq
        simp only [State.addr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
        omega

      have readable : InRegions (s.rd ++ s.wr)
          (off (State.addr P.B) (arr P.W wM) + BitVec.ofNat 64 i) 1 := by
        refine ⟨⟨State.addr P.B, P.Z⟩, List.mem_append_right _ hw.writable, ?_⟩
        rw [Offset.add_add]
        exact Offset.contains_base _ (by omega) (by omega)
      refine wp_ldrb (by decide) address readable fun s1 u1 => ?_
      obtain ⟨h1, hw1⟩ := h.reg hw (u1.rest (ws := [.r1]) (by simp)) u1.mem
      have mm1 := mm.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
      have value : (s1.gpr .r1).toNat = AW σ wM / 2 ^ (8 * i) % 256 := by
        rw [u1.gpr, BitVec.toNat_setWidth]
        rw [Nat.mod_eq_of_lt (Nat.lt_trans (s.mem _).isLt (by decide)), num_byte _ _ _ _ _ hi, h.arrsW wM hm]
      refine h1.strSlot_m mm1 hw1 (d := sByte) (r := .r1) (by decide)
        fun t ht mt hwt _ _ => WP.block_nil ⟨e, ?_, mt, hwt⟩
      rw [value] at ht
      exact ht

end
end VG.Proof.Rsa.Arm.Recover
