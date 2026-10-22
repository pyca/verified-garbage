module

public import VerifiedGarbage.Proof.RsaPss.X86.VfShift
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.X86.VfFixed
public import VerifiedGarbage.Proof.RsaPss.X86.VfTail

/-!
# RSASSA-PSS verification with a precomputed public key on x86: a salt of any length

As on ARMv7 (`Proof/RsaPss/Arm/VfAny.lean`): `DB` after `mHash` in `Y`
(`cpDb_vp`), shifted left by `pos + 1` bytes, so that `M'` is in `Y`
(`Ma`); its length and the blocks of the longest salt (`anyLen_vp`); and the
end of the paths (`any_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

/-- `M'`. -/
abbrev Ma (P : EP) (τ : State) : List Byte :=
  Spec.RsaPss.zeros 8 ++ digB h P τ ++ (dbL h P τ).drop (pzF h P τ + 1)

/-- Its blocks, those of the longest salt. -/
abbrev nbA (P : EP) : Nat := (dbN h P + (7 + h.D + h.L)) / h.B + 1

theorem pre_length (P : EP) (τ : State) : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
  simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]

theorem dbL_length (P : EP) (τ : State) : (dbL h P τ).length = dbN h P := by simp [dbL]

theorem Ma_length (P : EP) (τ : State) : (Ma h P τ).length = 8 + h.D + (dbN h P - (pzF h P τ + 1)) := by
  rw [Ma, List.length_append, pre_length, List.length_drop, dbL_length]

theorem Ma_getD {P : EP} {τ : State} {j : Nat} :
    (Ma h P τ).getD (8 + h.D + j) 0 = Dp h P τ (j + aV h P τ) := by
  rw [Ma, RsaPss.getD_app, pre_length, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD]
  unfold Dp aV
  by_cases e : j + (pzF h P τ + 1) < dbN h P
  · rw [ite_eq_left e, Nat.add_comm, ← dbL_getD h e]
  · rw [ite_eq_right e, getD_ge (by rw [dbL_length]; omega)]

/-- `DB` after `mHash`. -/
theorem cpDb_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem)
      (.seq (.block (cpDb h.H)) Impl.Bignum.X86.copyBytes)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem) ∧
      s.gpr .ebx = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
      s.gpr .ecx = BitVec.ofNat 32 (dbN h P))
    (VP.taint [.esp, .ebp] h.certs.cpDb (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hy⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := dbN h P) (by omega) (by omega))
      (hg.rbuf (o := oEm + lo P) (n := dbN h P) (by omega) (by omega))
      (by rw [hg.scrA (by omega), hg.scrA (by omega)]; exact Geo.sep (by omega) (by omega) (by omega)) (by omega)
      (f := fun τ i => dbF h P τ i)
      (Inv := fun τ m => Kq h P τ m ∧ ∀ j, dbN h P ≤ j → j < 2040 - h.D → m (sa P.scr (oY + 8 + h.D + j)) = 0)
      fun τ m m' ⟨hk, hz⟩ hf' => ?_).mono
      (fun τ s ⟨⟨hc, ⟨hk, _⟩, hy⟩, bx, si, cx⟩ => ⟨hc, ⟨⟨hk, fun i hi => hy i (by omega)⟩, fun j hj hj' => ?_⟩, bx, si,
        cx, fun i hi => ?_⟩)
      fun τ s ⟨hc, ⟨hk, hz⟩, hs⟩ => ⟨hc, hk, fun j hj => ?_⟩)
  · simp only [cpDb, atS, atDb, addSlot, addi, ld, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
    refine wp_mov fun t4 u4 => wp_addi fun t5 u5 => ?_
    have c5 : Ctx (P.lay h.D) P.scr τ t5 :=
      ((c2.upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)
    refine c5.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t6 c6 u6 => WP.block_nil ?_
    have m6 : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c6, m6 ▸ hk, m6 ▸ hy⟩, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u6.other, u5.gpr, u4.gpr, u3.other, u2.other, u1.other, hc.ebp]
    · simp (disch := decide) only [u6.other, u5.other, u4.other, u3.gpr, u2.gpr, u1.gpr, hc.ebp]
      rw [u2.mem, u1.mem, hg.aFr ok sLo (by decide), hk.1.2.2.1.2.1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    · rw [u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hk.1.2.2.1.2.2.1]
  · rw [hg.scrA (by omega)] at hf'
    refine ⟨⟨K2.keep h hk.1 hf' fun r hr => ?_, sbytes_keep hf' (fun r hr => ?_) (by omega) hk.2⟩,
      fun j hj hj' => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega) (by omega) (by omega)
    · rw [← hz j hj hj']
      exact hf' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega) (by omega) (by omega) _
          (Region.contains_self _ _)
  · rw [show oY + 8 + h.D + j = oY + (8 + h.D + j) by omega, hy _ (by omega)]
    exact getD_ge (by rw [pre_length]; omega)
  · rw [hg.byteAt_scr (by omega)]; exact hk.2.2.2.1 i hi
  · unfold Dp
    by_cases e : j < dbN h P
    · rw [ite_eq_left e, ← hs j e, hg.byteAt_scr (by omega)]
    · rw [ite_eq_right e]; exact hz j (by omega) hj

/-- `M'`'s length and blocks. -/
theorem anyLen_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) (.block (anyLen h.H))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Ma h P) (nbA h P) τ s.mem ∧
        ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Ma h P τ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.taint [.esp, .ebp] h.certs.anyLen (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi hk.1.2.1
  have hpz := pzF_lt h (τ := τ) hdb
  have hL := h.L_le
  have hB := h.B_ge
  have e3 : oY = 2048 := rfl
  have e1 : BitVec.ofNat 32 (dbN h P + (7 + h.D + h.L)) >>> lgB h.H =
      BitVec.ofNat 32 ((dbN h P + (7 + h.D + h.L)) / h.B) := by
    rw [ofNat_shr (by omega), h.pow_lg]
  have es : BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) = BitVec.ofNat 32 (dbN h P - pzF h P τ) :=
    Offset.ofNat_sub_ofNat (w := 32) (by omega)
  simp only [anyLen, ld, st, addi]
  refine hc.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t1 c1 u1 => ?_
  refine wp_subm (B := (P.lay h.D).B) (by rw [c1.st.sp])
    (by rw [hg.aFr ok sPos (by decide)]; exact c1.rFr hg sPos (by decide)) fun t2 u2 => ?_
  refine wp_addi fun t3 u3 => ((c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).wp_st hg
    (d := sL) (by decide) fun t4 c4 m4 => ?_
  refine c4.wp_slot hg (d := sDb) (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine wp_addi fun t6 u6 => wp_shr h.lg_range fun t7 u7 _ => wp_addi fun t8 u8 => ?_
  refine (((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).upd u8 (by decide)
    (by decide)).wp_st hg (d := sNb) (by decide) fun t9 c9 m9 => WP.block_nil ?_
  have v3 : t3.gpr .eax = BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D)) := by
    rw [u3.gpr, u2.gpr, u1.gpr, u1.mem, hg.aFr ok sPos (by decide), hk.1.2.2.1.2.2.1, hk.1.2.2.2.2.2.1, es,
      BitVec.ofNat_add_ofNat]
  have m4' : t4.mem = s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D))) := by
    rw [m4.mem, v3, u3.mem, u2.mem, u1.mem]
  have v8 : t8.gpr .eax = BitVec.ofNat 32 (nbA h P) := by
    rw [u8.gpr, u7.gpr, u6.gpr, u5.gpr, m4', Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      hk.1.2.2.1.2.2.1, BitVec.ofNat_add_ofNat, show dbN h P + (7 + h.D + h.L) = dbN h P + (7 + h.D + h.L) from rfl,
      e1, BitVec.ofNat_add_ofNat]
  have m : t9.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D)))).writeW
      ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbA h P)) := by
    rw [m9.mem, v8, u8.mem, u7.mem, u6.mem, u5.mem, m4']
  have fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t9.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  have aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  have hy' := sbytes_keep fr (aw _ _ (by omega)) (by omega) hy
  have hp' := sbytes_keep fr (aw _ _ (by omega)) (by omega) hk.2
  refine ⟨c9, ⟨K2.keep h hk.1 fr fun r hr => ?_, ?_, ?_⟩, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · rw [m, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Ma_length]
    congr 1; omega
  · rw [m, Mem.readW_writeW_self32]
  · by_cases e : i < 8 + h.D
    · rw [hp' i e, Ma, RsaPss.getD_app (l := Spec.RsaPss.zeros 8 ++ digB h P τ), pre_length, ite_eq_left e]
    · have := hy' (i - (8 + h.D)) (by omega)
      rw [show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega] at this
      rw [this, show i = 8 + h.D + (i - (8 + h.D)) by omega, Ma_getD]
      congr 1; omega

/-- A salt of any length. -/
theorem any_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ True) (anyPath h.H)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (Ma h P τ) then 1 else 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.2.1
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hL := h.L_le
  have hB := h.B_le
  have hB0 : 0 < h.B := by have := h.B_ge; omega
  obtain ⟨hlo, hdb, hdD, hD', hD0⟩ := shB h hi₀ hf
  have q1 := Nat.lt_mul_div_succ (dbN h P + (7 + h.D + h.L)) hB0
  have q2 := Nat.mul_div_le (dbN h P + (7 + h.D + h.L)) h.B
  have hT : nbA h P * h.B ≤ 2048 := by
    show ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega
  show VP _ (.seq (yDig h.H 4) (.seq (.block (cpDb h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq (shift h.H)
    (.seq (.block (anyLen h.H)) (.seq (ctHash h.H) (cmpH h.H))))))) _
  refine (yDig_vf h P ⟨σ₀, hi₀⟩ True).seq (Sg.vpAssoc ((cpDb_vp h P ⟨σ₀, hi₀⟩).seq ((shift_vp h P ⟨σ₀, hi₀⟩).seq
    ((anyLen_vp h P ⟨σ₀, hi₀⟩).seq ?_))))
  exact (tail_vp h P ⟨σ₀, hi₀⟩ hT (Nat.succ_pos _) (msg := Ma h P) fun τ => by
      rw [Ma_length]; show _ ≤ ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega).mono
    (fun τ s ⟨hc, hk, hy⟩ => ⟨hc, hk, fun i hi => hy i (by omega)⟩) fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, r0⟩

end VG.Proof.RsaPss.X86.Vf
