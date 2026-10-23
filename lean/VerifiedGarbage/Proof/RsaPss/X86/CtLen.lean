module

public import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS on x86: hashing, the block of the length field

`lenBlk_vp`: the block at `oLen` cleared, then the length field of `ℓ` (in
the slot `sL`) written in its last 8 bytes (`len64Of`): its bytes are
`lenBlk` of the length field (`LB`, by `PssHash.len`); and the index of the
last block of the padded message to the slot `sLb`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The block at `oLen` holds zeros and the length field of `ℓ`. -/
def LB (scr : BitVec 32) (ℓ : Nat) (m : Mem) : Prop :=
  ∀ j < h.B, m (sa scr (oLen + j)) = lenBlk h.B h.L (h.md.lenBytes ℓ) j

theorem ofNat_shr {k n : Nat} (hk : k < 2 ^ 32) : BitVec.ofNat 32 k >>> n = BitVec.ofNat 32 (k / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hk)]

theorem count0 {ℓ : Nat} (hℓ : ℓ < 2 ^ 32) : (0#32 ++ BitVec.ofNat 32 ℓ).toNat = ℓ := by
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, Nat.mod_eq_of_lt hℓ]

/-- The block at `oLen` and the last block's index. -/
theorem lenBlk_vp (hg : Geo L scr) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oLen h.B, slotR L sLb] m m' → Inv σ m') {ℓ : State → Nat}
    (hℓ : ∀ σ, ℓ σ < 2 ^ 29) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ))
      (lenPart h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ LB h scr (ℓ σ) s.mem ∧
        s.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ) ∧
        s.mem.readW (L.fr sLb) 32 = BitVec.ofNat 32 ((ℓ σ + h.L) / h.B)) := by
  have hN := h.N_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hL8 := h.L8
  have hNL := h.NL
  have fit := hg.fit
  unfold oRsa at fit
  have eB : h.H.B = h.B := rfl
  have eB' : h.H.st.B = h.B := rfl
  have eL : h.H.L = h.L := rfl
  obtain ⟨σ', ok⟩ := hg.ok
  have dLs : (sR scr oLen h.B).Disjoint (slotR L sL) := (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  have dLb : (sR scr oLen h.B).Disjoint (slotR L sLb) := (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  let I₁ : State → Mem → Prop := fun σ m => Inv σ m ∧ m.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ)
  have hI₁ : ∀ σ m m', I₁ σ m → Frame [⟨(scr + BitVec.ofNat 32 oLen).setWidth 64, h.B⟩] m m' → I₁ σ m' :=
    fun σ m m' ⟨hi, hs⟩ fr => by
      rw [hg.scrA (by decide)] at fr
      exact ⟨hI σ _ _ hi (fr.mono (by simp)), slot_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dLs.symm) hs⟩
  -- The block cleared.
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ I₁ σ s.mem ∧ s.gpr .esi = scr + BitVec.ofNat 32 oLen ∧
      s.gpr .ecx = BitVec.ofNat 32 h.B ∧ s.gpr .eax = 0)
    (VP.taint [.esp, .ebp] h.certs.clrB (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, hs⟩ => ?_) ?_
  · simp only [clrArgs, atS, mi, addi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
    refine ⟨(((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
      (by decide)).upd u4 (by decide) (by decide), ⟨?_, ?_⟩, ?_, ?_, u4.gpr⟩
    · rw [u4.mem, u3.mem, u2.mem, u1.mem]; exact hi
    · rw [u4.mem, u3.mem, u2.mem, u1.mem]; exact hs
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr, hc.ebp]
    · rw [u4.other _ (by decide), u3.gpr]
  refine VP.seq (VP.mono (zero_vp (hg.wbuf (o := oLen) (n := h.B) (by pomega) (by omega_arith)) (by omega_arith) hI₁)
    (fun _ _ h => h) fun _ _ h => h) ?_
  -- The length field and the last block.
  refine VP.taint [.esp, .ebp] h.certs.lenSet (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hi, hs⟩, hz⟩ => ?_
  have hz' : ∀ j < h.B, s.mem (sa scr (oLen + j)) = 0 := fun j hj => by
    rw [← hz j hj, hg.byteAt_scr (by pomega)]
  simp only [lenSet, atS, ld, mi, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine c2.wp_slot hg (d := sL) (by decide) (by decide) (by decide) fun t3 c3 u3 => wp_movi fun t4 u4 => ?_
  have c4 := c3.upd u4 (by decide) (by decide)
  have bx4 : t4.gpr .ebx = scr + BitVec.ofNat 32 oLen := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr, hc.ebp]
  have ax4 : t4.gpr .eax = BitVec.ofNat 32 (ℓ σ) := by
    rw [u4.other _ (by decide), u3.gpr, u2.mem, u1.mem, hs]
  have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have hfit : (t4.gpr .ebx).toNat + (h.H.B - 8) + 8 ≤ 2 ^ 32 := by rw [bx4, hg.scr_lt (by decide)]; pomega
  have e8 : (t4.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (h.H.B - 8) = sa scr (oLen + (h.B - 8)) := by
    rw [bx4, hg.scrA (by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hw1 : InRegions t4.wr (VG.X86.addr (t4.gpr .ebx) (h.H.B - 8)) 4 := by
    rw [addr_eq (by omega_arith), e8]; exact hg.wr c4.st (by pomega)
  have hw2 : InRegions t4.wr (VG.X86.addr (t4.gpr .ebx) (h.H.B - 8 + 4)) 4 := by
    rw [addr_eq (by omega_arith), bx4, hg.scrA (by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact hg.wr c4.st (by pomega)
  refine WP.block_append ((Proof.MdStream.X86.len64Of_ok hfit ax4 u4.gpr hw1 hw2).mono fun t5 ⟨g5, rd5, wr5, m5⟩ => ?_)
  have hl8 := Proof.MdStream.bytes64_length h.H.be (BitVec.ofNat 64 (8 * ((0 : BitVec 32) ++ BitVec.ofNat 32 (ℓ σ)).toNat))
  have fr5 : Frame [sR scr (oLen + (h.B - 8)) 8] t4.mem t5.mem := by
    rw [m5, e8]
    have := VG.WriteBytes.writeBytes_frame t4.mem (sa scr (oLen + (h.B - 8)))
      (Proof.MdStream.bytes64 h.H.be (BitVec.ofNat 64 (8 * ((0 : BitVec 32) ++ BitVec.ofNat 32 (ℓ σ)).toNat)))
      (R := sR scr (oLen + (h.B - 8)) 8) (by rw [hl8]; exact Region.contains_self _ _)
    exact this
  have sub8 : Region.Sub (sR scr (oLen + (h.B - 8)) 8) (sR scr oLen h.B) := Offset.sub _ (by omega_arith) (by omega_arith)
  have c5 : Ctx L scr σ t5 := c4.write fr5 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega))
    rd5 wr5 (g5 _ (by decide) (by decide) (by decide)) (g5 _ (by decide) (by decide) (by decide))
  have dS8 : (sR scr (oLen + (h.B - 8)) 8).Disjoint (slotR L sL) := dLs.sub_left sub8
  have sl5 : t5.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ) :=
    slot_keep fr5 (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS8.symm)
      (by rw [m4]; exact hs)
  refine c5.wp_slot hg (d := sL) (by decide) (by decide) (by decide) fun t6 c6 u6 => wp_addi fun t7 u7 => ?_
  refine wp_shr h.lg_range fun t8 u8 _ => ?_
  have c8 := (c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)
  refine c8.wp_st hg (d := sLb) (by decide) fun t9 c9 m9 => WP.block_nil ?_
  have ax8 : t8.gpr .eax = BitVec.ofNat 32 ((ℓ σ + h.L) / h.B) := by
    rw [u8.gpr, u7.gpr, u6.gpr, sl5, BitVec.ofNat_add_ofNat, ofNat_shr (by have := hℓ σ; omega_arith), h.pow_lg]
  have m8 : t8.mem = t5.mem := by rw [u8.mem, u7.mem, u6.mem]
  have fr9 : Frame [slotR L sLb] t5.mem t9.mem := by rw [m9.mem, m8]; exact slot_frame L _ _ _
  refine ⟨c9, hI σ _ _ hi ?_, fun j hj => ?_, ?_, ?_⟩
  · have f1 : Frame [sR scr oLen h.B, slotR L sLb] s.mem t5.mem := by
      rw [← m4]; exact fr5.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, sub8⟩
    exact f1.trans (fr9.mono (by simp))
  · have dj : (sR scr (oLen + j) 1).Disjoint (slotR L sLb) :=
      (hg.slot ok (o := oLen + j) (n := 1) (by pomega) (by rw [hg.F]; decide)).symm
    rw [fr9 (sa scr (oLen + j)) (fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dj _ (Region.contains_self _ _) hcon), m5, e8]
    simp only [VG.WriteBytes.writeBytes, Proof.MdStream.bytes64_length, lenBlk, h.len _ (hℓ σ), m4]
    have e : sa scr (oLen + j) - sa scr (oLen + (h.B - 8)) =
        BitVec.ofNat 64 (18446744073709551616 - (h.B - 8) + j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [sa, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (scr.setWidth 64).isLt
      pomega
    rw [e, BitVec.toNat_ofNat]
    by_cases hj' : j < h.B - 8
    · rw [ite_eq_right (by omega_arith), hz' j hj]
      by_cases hj'' : j < h.B - h.L
      · rw [ite_eq_left hj'']
      · rw [ite_eq_right hj'', Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by simp; omega_arith),
          List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left (by omega_arith)]
        rfl
    · rw [ite_eq_left (by omega_arith), ite_eq_right (by omega_arith),
        Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp; omega_arith), List.length_replicate,
        count0 (show ℓ σ < 2 ^ 32 by have := hℓ σ; omega_arith)]
      congr 1; omega_arith
  · rw [fr9.readW (r := slotR L sL) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by left; decide) (by decide) (by decide)) (by decide)]
    exact sl5
  · rw [m9.mem, Mem.readW_writeW_self32, ax8]

end VG.Proof.RsaPss.X86
