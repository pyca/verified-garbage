module

public import VerifiedGarbage.Proof.RsaPss.X86.VfTail
public import VerifiedGarbage.Proof.RsaPss.X86.YDig
import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
import VerifiedGarbage.Proof.RsaPss.X86.CtLoop
import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.Prims
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification with a precomputed public key on x86: a salt of the expected length

As on ARMv7 (`Proof/RsaPss/Arm/VfY.lean`, `VfFixed.lean`): `Y` cleared and
`mHash` after its 8 zero bytes (`yDig_vf`); the last `sLen` bytes of `DB`
after it (`fxSalt_vp`), `M'`'s length and blocks (`lenF_vp`), and the end of
the paths (`fixed_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.RsaPss.X86.Sg (add_ofNat_sub)

variable (h : PssHash)

theorem dig_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.dig h.D := by
  obtain ⟨σ, hi⟩ := hP
  have hf := hi.ok.fits (P.DIG h.D) (by simp)
  simp only [BitVec.toNat_setWidth] at hf
  rw [Nat.mod_eq_of_lt (by have := P.dig.isLt; omega)] at hf
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  exact ⟨hf, by omega, ⟨P.DIG h.D, by simp, Region.contains_self _ _⟩⟩

/-- `Y`: 8 zero bytes and `mHash`. -/
abbrev Y1 (P : EP) (τ : State) (m : Mem) : Prop :=
  ∀ i < 2048, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0

/-- `Y` cleared and `mHash` after its 8 zero bytes. -/
theorem yDig_vf (P : EP) (hP : ∃ σ, In h.D P σ) (Q : Prop) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ Q) (yDig h.H 4)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ Q) ∧ Y1 h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine (yDig_vp h hg (j := 4) h.certs.cpDig4 (by simp) (dgP := P.dig) rfl (dig_buf h ⟨σ₀, hi₀⟩)
    (fun o n hon => (hg.ro ok hon (R := P.DIG h.D) (by simp)).symm) (dl := digB h P)
    (fun σ => RsaPkcs1Sig.bytesAt_len _ _ _) (fun σ s hc i hi => ?_) (X := fun τ m => K2 h P τ m ∧ Q)
    fun σ m m' ⟨hk, hq⟩ hf => ⟨K2.keep h hk hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by decide) (by decide), hq⟩).mono
    (fun σ s ⟨hc, hk, hq⟩ => ⟨hc, hk, hq⟩) fun σ s h' => h'
  have e : Spec.Rsa.bytesAt s.mem (P.dig.setWidth 64) h.D = Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D :=
    hc.st.ro (R := P.DIG h.D) (by simp)
  show s.mem (P.dig.setWidth 64 + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (P.dig.setWidth 64) h.D).getD i 0
  rw [← e, RsaPkcs1Sig.bytesAt_getD hi]

/-- The last `sLen` bytes of `DB`. -/
abbrev sltB (P : EP) (τ : State) : List Byte := (List.range P.slt).map fun i => dbF h P τ (dbN h P - P.slt + i)

/-- `M'`. -/
abbrev Mf (P : EP) (τ : State) : List Byte := Spec.RsaPss.zeros 8 ++ digB h P τ ++ sltB h P τ

/-- Its blocks. -/
abbrev nbF (P : EP) : Nat := (P.slt + (8 + h.D) + h.L) / h.B + 1

/-- `Y`, with `M'`. -/
abbrev Yf (P : EP) (τ : State) (m : Mem) : Prop := ∀ i < 2048, m (sa P.scr (oY + i)) = (Mf h P τ).getD i 0

theorem Mf_length (P : EP) (τ : State) : (Mf h P τ).length = P.slt + (8 + h.D) := by
  simp only [Mf, List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len, sltB,
    List.length_map, List.length_range]; omega

/-- What the fixed path starts from. -/
abbrev F0 (P : EP) (τ s : State) : Prop := Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Y1 h P τ s.mem

/-- The last `sLen` bytes of `DB` after `mHash`. -/
theorem fxSalt_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (F0 h P) (.seq (.block (fxSalt h.H)) (.ite .e (.block []) Impl.Bignum.X86.copyBytes))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Yf h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P ∧ P.any = 0
  swap
  · exact VP.empty fun σ s h' => hf ⟨h'.2.1.1.2.1, h'.2.1.2⟩
  obtain ⟨hf, ha⟩ := hf
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have hsl := hi₀.slt32
  refine VP.seq (G := fun τ s => F0 h P τ s ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.slt) ∧ s.gpr .ecx = BitVec.ofNat 32 P.slt ∧
      s.zf = some (decide (P.slt = 0)))
    (VP.taint [.esp, .ebp] h.certs.fxSalt (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, ⟨hk, ha'⟩, hy⟩ => ?_)
    (VP.ite (fun σ s h' => ⟨_, h'.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2.2.2, h₂.2.2.2.2])
      (VP.block_nil fun τ s ⟨⟨⟨hc, hk, hy⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_)
  · simp only [fxSalt, atDb, atS, addSlot, addi, ld, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
      List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx (P.lay h.D) P.scr τ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
    have c3 : Ctx (P.lay h.D) P.scr τ t3 := c2.upd u3 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c3.st.sp])
      (by rw [hg.aFr ok sDb (by decide)]; exact c3.rFr hg sDb (by decide)) fun t4 u4 => ?_
    have c4 : Ctx (P.lay h.D) P.scr τ t4 := c3.upd u4 (by decide) (by decide)
    refine wp_subm (B := (P.lay h.D).B) (by rw [c4.st.sp]) (by rw [hg.aArg ok 7 (by simp)]; exact
      (by rw [c4.st.rd, c4.st.wr]; exact c4.st.ok.arg_read (vf_arg h (by decide)))) fun t5 u5 => ?_
    refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => ?_
    have c7 : Ctx (P.lay h.D) P.scr τ t7 :=
      ((c4.upd u5 (by decide) (by decide)).upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)
    refine c7.wp_arg hg (vf_arg h (j := 7) (by decide)) (by decide) (by decide) fun t8 c8 u8 =>
      wp_test fun t9 f9 z9 => WP.block_nil ?_
    have m9 : t9.mem = s.mem := by rw [f9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c8.fupd f9, m9 ▸ ⟨hk, ha'⟩, m9 ▸ hy⟩, ?_, ?_, ?_, ?_⟩
    · rw [f9.gpr]
      simp (disch := decide) only [u8.other, u7.gpr, u6.gpr, u5.other, u4.other, u3.other, u2.other, u1.other,
        hc.ebp]
    · rw [f9.gpr]
      simp (disch := decide) only [u8.other, u7.other, u6.other, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr, hc.ebp]
      rw [u4.mem, u3.mem, u2.mem, u1.mem, hg.aFr ok sLo (by decide), hk.2.2.1.2.1, hg.aFr ok sDb (by decide),
        hk.2.2.1.2.2.1, hg.aArg ok 7 (by simp), hc.st.arg (vf_arg h (by decide)),
        show (P.lay h.D).argv.getD 7 0 = BitVec.ofNat 32 P.slt from rfl, BitVec.add_assoc, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, add_ofNat_sub (by omega), Nat.add_assoc]
    · rw [f9.gpr, u8.gpr]; rfl
    · rw [z9, u8.gpr, BitVec.and_self]
      exact congrArg some (ofNat_beq_zero hsl)
  · have h0 : P.slt = 0 := by
      simp only [eval, z, Option.some.injEq, decide_eq_true_eq] at e; exact e
    rw [hy i hi]
    simp [Mf, sltB, h0]
  · by_cases h0 : P.slt = 0
    · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
        simp only [eval, z, decide_eq_true h0] at e; exact absurd e (by decide)
    refine (copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := P.slt) (by omega) (by omega))
      (hg.rbuf (o := oEm + lo P + dbN h P - P.slt) (n := P.slt) (by omega) (by omega))
      (by rw [hg.scrA (by omega), hg.scrA (by omega)]; exact Geo.sep (by omega) (by omega) (by omega)) (by omega)
      (f := fun τ i => dbF h P τ (dbN h P - P.slt + i))
      (Inv := fun τ m => (K2 h P τ m ∧ P.any = 0) ∧
        (∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0) ∧
        YZ P.scr (8 + h.D + P.slt) m) fun τ m m' ⟨⟨hk, ha'⟩, h1, h2⟩ hf' => ?_).mono
      (fun τ s ⟨⟨⟨hc, hk, hy⟩, bx, si, cx, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi => hy i (by omega), fun i hi => ?_⟩, bx, si, cx,
        fun i hi => ?_⟩) fun τ s ⟨hc, ⟨hk, h1, h2⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
    · rw [hg.scrA (by omega)] at hf'
      refine ⟨⟨K2.keep h hk hf' fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega) (by omega), ha'⟩,
        sbytes_keep hf' (fun r hr => ?_) (by omega) h1, sbytes_keep hf' (fun r hr => ?_) (by omega) h2⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega) (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega) (by omega) (by omega)
    · rw [show oY + (8 + h.D + P.slt) + i = oY + (8 + h.D + P.slt + i) by omega, hy _ (by omega),
        getD_ge (by simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]; omega)]
    · rw [hg.byteAt_scr (by omega), show oEm + lo P + dbN h P - P.slt + i = oEm + lo P + (dbN h P - P.slt + i) by omega]
      exact hk.1.2.2.2.1 _ (by omega)
    · have hl : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
        simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.bytesAt_len]
      rw [RsaPss.getD_app, hl]
      by_cases e1 : i < 8 + h.D
      · rw [ite_eq_left e1]; exact h1 i e1
      rw [ite_eq_right e1]
      by_cases e2 : i < 8 + h.D + P.slt
      · have e := hs (i - (8 + h.D)) (by omega)
        rw [hg.byteAt_scr (by omega), show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega] at e
        rw [e]
        simp [sltB, List.getD_eq_getElem?_getD, show i - (8 + h.D) < P.slt by omega]
      · rw [getD_ge (l := sltB h P τ) (by simp only [sltB, List.length_map, List.length_range]; omega),
          show oY + i = oY + (8 + h.D + P.slt) + (i - (8 + h.D + P.slt)) by omega]
        exact h2 _ (by omega)

/-- `M'`'s length and blocks. -/
theorem lenF_vp (P : EP) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Yf h P τ s.mem)
      (.block (lenArgs h.H 7))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Mf h P) (nbF h P) τ s.mem ∧ Yf h P τ s.mem) := by
  refine VP.taint [.esp, .ebp] h.certs.lenArgs7 (sp_bp fun _ _ h => h.1) fun τ s ⟨hc, ⟨hk, ha⟩, hy⟩ => ?_
  have hg := hk.1.geo
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hL := h.L_le
  have hB := h.B_ge
  have hsl := hk.1.slt32
  obtain ⟨hlo, hdb, hsum, hK, hD', hD0, hK0⟩ := fitB h hk.1 hk.2.1
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have e1 : BitVec.ofNat 32 (P.slt + (8 + h.D) + h.L) >>> lgB h.H =
      BitVec.ofNat 32 ((P.slt + (8 + h.D) + h.L) / h.B) := by
    rw [ofNat_shr (by omega), h.pow_lg]
  obtain ⟨σ', ok⟩ := hg.ok
  simp only [lenArgs, ld, st, addi]
  refine hc.wp_arg hg (vf_arg h (j := 7) (by decide)) (by decide) (by decide) fun t1 c1 u1 =>
    wp_addi fun t2 u2 => (c1.upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 u3 =>
      wp_addi fun t4 u4 => wp_shr h.lg_range fun t5 u5 _ => wp_addi fun t6 u6 => ?_
  refine ((((c3.upd u4 (by decide) (by decide)).upd u5 (by decide) (by decide)).upd u6 (by decide)
    (by decide))).wp_st hg (by decide) fun t7 c7 u7 => WP.block_nil ?_
  have e2 : t2.gpr .eax = BitVec.ofNat 32 (P.slt + (8 + h.D)) := by
    rw [u2.gpr, u1.gpr]; exact BitVec.ofNat_add_ofNat ..
  have e6 : t6.gpr .eax = BitVec.ofNat 32 (nbF h P) := by
    rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, e2, BitVec.ofNat_add_ofNat]
    show BitVec.ofNat 32 (P.slt + (8 + h.D) + h.L) >>> lgB h.H + _ = _
    rw [e1, BitVec.ofNat_add_ofNat]
  have m7 : t7.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (P.slt + (8 + h.D)))).writeW
      ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbF h P)) := by
    rw [u7.mem, e6, u6.mem, u5.mem, u4.mem, u3.mem, e2, u2.mem, u1.mem]
  have fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t7.mem := by
    rw [m7]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨c7, ⟨K2.keep h hk fr fun r hr => ?_, ?_, ?_⟩, sbytes_keep fr (fun r hr => ?_) (by pomega) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · rw [m7, Lay.readW_fr_other (d := sL) (e := sNb) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Mf_length]
  · rw [m7, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm

/-- A salt of the expected length. -/
theorem fixed_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ P.any = 0) (fixedPath h.H)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .eax = if acc2 h P τ = 0 ∧ HOk h P τ (Mf h P τ) then 1 else 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P ∧ P.any = 0
  swap
  · exact VP.empty fun σ s h' => hf ⟨h'.2.1.2.1, h'.2.2⟩
  obtain ⟨hf, ha⟩ := hf
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hL := h.L_le
  have hB := h.B_le
  have hB0 : 0 < h.B := by have := h.B_ge; omega
  obtain ⟨hlo, hdb, hsum, hK, hD', hD0, hK0⟩ := fitB h hi₀ hf
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have q1 := Nat.lt_mul_div_succ (P.slt + (8 + h.D) + h.L) hB0
  have q2 := Nat.mul_div_le (P.slt + (8 + h.D) + h.L) h.B
  have hT : nbF h P * h.B ≤ 2048 := by
    show ((P.slt + (8 + h.D) + h.L) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega
  show VP _ (.seq (yDig h.H 4) (.seq (.block (fxSalt h.H)) (.seq (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
    (.seq (.block (lenArgs h.H 7)) (.seq (ctHash h.H) (cmpH h.H)))))) _
  refine (yDig_vf h P ⟨σ₀, hi₀⟩ (P.any = 0)).seq ?_
  refine Sg.vpAssoc ((fxSalt_vp h P ⟨σ₀, hi₀⟩).seq ((lenF_vp h P).seq ?_))
  exact (tail_vp h P ⟨σ₀, hi₀⟩ hT (Nat.succ_pos _) (msg := Mf h P) fun τ => by
      rw [Mf_length]; show _ ≤ ((P.slt + (8 + h.D) + h.L) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega).mono
    (fun τ s ⟨hc, hk, hy⟩ => ⟨hc, hk, fun i hi => hy i (by omega)⟩) fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, r0⟩

end VG.Proof.RsaPss.X86.Vf
