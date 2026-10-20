module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSASSA-PSS on ARMv7: hashing, the block of the length field

`lenBlk_vp`: the block at `oLen` cleared, then the length field of `ℓ` (in
the slot `sL`) written at its end: its bytes are `lenBlk` of the length
field (`LB`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The block at `oLen` holds zeros and the length field of `ℓ`. -/
def LB (scr : BitVec 32) (ℓ : Nat) (m : Mem) : Prop :=
  ∀ j < h.B, m (sa scr (oLen + j)) = lenBlk h.B h.L (h.md.lenBytes ℓ) j

theorem count0 {ℓ : Nat} (hℓ : ℓ < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 ℓ = BitVec.ofNat 64 ℓ := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hℓ,
    Nat.mod_eq_of_lt (by omega)]
  simp

theorem lenBlk_vp (hg : Geo L scr) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oLen h.B] m m' → Inv σ m') {ℓ : State → Nat}
    (hℓ : ∀ σ, ℓ σ < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ))
      (.seq (.block (lenClr h.H)) (.seq Impl.Bignum.Arm.maskBytes (.seq (.block (lenArgs h.H)) (.block h.H.len))))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ LB h scr (ℓ σ) s.mem) := by
  have hN := h.N_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hNL := h.NL
  have fit := hg.fit
  have eN : h.H.md.N = h.N := rfl
  have eB : h.H.md.B = h.B := rfl
  have eL : h.H.md.L = h.L := rfl
  unfold oRsa at fit
  let I₁ : State → Mem → Prop := fun σ m => Inv σ m ∧ m.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ)
  have hI₁ : ∀ σ m m', I₁ σ m → Frame [⟨State.addr (scr + BitVec.ofNat 32 oLen), h.B⟩] m m' → I₁ σ m' :=
    fun σ m m' ⟨hi, hs⟩ fr => by
      rw [hg.addr (by decide)] at fr
      obtain ⟨σ', ok⟩ := hg.ok
      exact ⟨hI σ _ _ hi fr, slot_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hg.slot ok (by pomega) (by rw [hg.F]; decide)) hs⟩
  -- The block cleared.
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ I₁ σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oLen ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 h.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hs⟩ => ?_) ?_
  · prun [lenClr, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi, hs,
      movw_val (show oLen < 2 ^ 16 by decide), movw_val (show h.B < 2 ^ 16 by omega)]
    exact ⟨hi, hs⟩
  refine VP.seq (VP.mono (zero_vp (hg.wbuf (o := oLen) (n := h.B) (by pomega) (by omega))
    (by omega) hI₁) (fun _ _ h => h) fun _ _ h => h) ?_
  -- The length field.
  let I₂ : State → Mem → Prop := fun σ m => Inv σ m ∧ ∀ j < h.B - h.L, m (sa scr (oLen + j)) = 0
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ (Inv σ s.mem ∧ ∀ j < h.B, s.mem (sa scr (oLen + j)) = 0) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 (oLen - h.N) ∧ s.gpr .r4 = BitVec.ofNat 32 (ℓ σ) ∧ s.gpr .r5 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, ⟨hi, hs⟩, hz⟩ => ?_) ?_
  · have hz' : ∀ j < h.B, s.mem (sa scr (oLen + j)) = 0 := fun j hj => by
      rw [← hz j hj, hg.byteAt_scr (by pomega)]
    prun [lenArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi, hs,
      movw_val (show oLen - h.N < 2 ^ 16 by pomega), movw_val (show 0 < 2 ^ 16 by decide)]
    exact ⟨hz', rfl⟩
  refine VP.taint [.r0] h.lenCk (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) fun σ s ⟨hc, ⟨hi, hz⟩, r0, r4, r5⟩ => ?_
  have a0 : State.addr (s.gpr .r0) = sa scr (oLen - h.N) := by rw [r0, hg.addr (by pomega)]
  have e0 : State.addr (s.gpr .r0) + BitVec.ofNat 64 (h.N + (h.B - h.L)) = sa scr (oLen + (h.B - h.L)) := by
    rw [a0, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; unfold oLen; omega
  refine WP.mono (h.len s (by rw [r0, hg.scr_lt (by pomega)]; pomega)
    (by rw [e0]; exact hg.wr hc.st (by pomega))) fun t ⟨g, rd, wr, sp, m⟩ => ?_
  rw [e0, r4, r5, count0 (hℓ σ), h.md.lenOf_eq _ (h.lenAll _ (hℓ σ))] at m
  have hlen := h.md.lenBytes_length (ℓ σ)
  have fr : Frame [sR scr (oLen + (h.B - h.L)) h.L] s.mem t.mem := by
    rw [m]
    refine (Frame.refl _ _).trans ?_
    intro a ha
    simp only [List.mem_singleton, forall_eq, Region.Contains, VG.WriteBytes.writeBytes, hlen] at ha ⊢
    rw [ite_eq_right (by omega)]
  have hsub : Region.Sub (sR scr (oLen + (h.B - h.L)) h.L) (sR scr oLen h.B) :=
    Offset.sub _ (by omega) (by omega)
  have fr' : Frame [sR scr oLen h.B] s.mem t.mem := fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hc.write fr' (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hI σ _ _ hi fr', fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact hg.slot ok (by pomega) (by rw [hg.F]; decide)
  · rw [m]
    simp only [VG.WriteBytes.writeBytes, lenBlk, hlen]
    have e : sa scr (oLen + j) - sa scr (oLen + (h.B - h.L)) = BitVec.ofNat 64 (2 ^ 64 - (h.B - h.L) + j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [sa, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (State.addr scr).isLt
      pomega
    by_cases hj' : j < h.B - h.L
    · rw [ite_eq_left hj', ite_eq_right (by rw [e, BitVec.toNat_ofNat]; omega), hz j hj]
    · rw [ite_eq_right hj', ite_eq_left (by rw [e, BitVec.toNat_ofNat]; omega), e, BitVec.toNat_ofNat]
      congr 1; omega

end VG.Proof.RsaPss.Arm
