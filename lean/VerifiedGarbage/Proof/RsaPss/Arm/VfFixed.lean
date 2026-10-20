module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfY
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.YDig
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: a salt of the expected length

`M' = 0⁸ ‖ mHash ‖` the last `sLen` bytes of `DB` (`Mf`), hashed and compared
with `H` (`fixed_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (add_ofNat_sub)

variable (h : PssHash)

/-- The last `sLen` bytes of `DB`. -/
abbrev sltB (P : EP) (τ : State) : List Byte := (List.range P.slt).map fun i => dbF h P τ (dbN h P - P.slt + i)

/-- `M'`. -/
abbrev Mf (P : EP) (τ : State) : List Byte := Spec.RsaPss.zeros 8 ++ digB h P τ ++ sltB h P τ

/-- Its blocks. -/
abbrev nbF (P : EP) : Nat := (P.slt + (8 + h.D) + h.L) / h.B + 1

/-- `Y`, with `M'`. -/
abbrev Yf (P : EP) (τ : State) (m : Mem) : Prop := ∀ i < 2048, m (sa P.scr (oY + i)) = (Mf h P τ).getD i 0

theorem Mf_length (P : EP) (τ : State) : (Mf h P τ).length = P.slt + (8 + h.D) := by
  simp only [Mf, List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length, sltB,
    List.length_map, List.length_range]; omega

/-- What the fixed path starts from. -/
abbrev F0 (P : EP) (τ s : State) : Prop := Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Y1 h P τ s.mem

/-- The last `sLen` bytes of `DB` after `mHash`. -/
theorem fxSalt_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (F0 h P) (.seq (.block (fxSalt h.H)) (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes))
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
  refine VP.seq (G := fun τ s => F0 h P τ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.slt) ∧ s.gpr .lr = BitVec.ofNat 32 P.slt ∧
      s.z = decide (P.slt = 0))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, ⟨hk, ha'⟩, hy⟩ => ?_)
    (VP.ite (fun _ _ _ _ h₁ h₂ => by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2.2.2.2,
      h₂.2.2.2.2]) (VP.block_nil fun τ s ⟨⟨⟨hc, hk, hy⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_)
  · obtain ⟨a7, r7, v7⟩ := argAt hk.1 hc.st (j := 7) (by decide)
    replace v7 : s.mem.readW ((P.lay h.D).fr (arg 7)) 32 = BitVec.ofNat 32 P.slt := v7
    have hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
    have hw : WP isa (.block (fxSalt h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.slt) ∧
        t.gpr .lr = BitVec.ofNat 32 P.slt ∧ t.z = decide (P.slt = 0) := by
      prun [fxSalt, atS, atDb, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a7, r7, v7, arg_lt,
        hk.2.2.1.2.1, hk.2.2.1.2.2.1,
        movw_val (show oY + 8 + dig h.H < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; omega),
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat, hz0,
        add_ofNat_sub (x := P.scr) (a := oEm + lo P + dbN h P) (b := P.slt) (by omega),
        VG.Proof.X25519.Arm.ofNat_beq_zero hsl]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, z⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ ⟨hk, ha'⟩, m ▸ hy⟩, r0, r1, lr, z⟩
  · have h0 : P.slt = 0 := by
      rw [VG.Proof.X25519.Arm.eval_eq, z] at e; simpa using e
    rw [hy i hi]
    simp [Mf, sltB, h0]
  · by_cases h0 : P.slt = 0
    · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true h0] at e; exact absurd e (by decide)
    refine (copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := P.slt) (by omega) (by omega))
      (hg.rbuf (o := oEm + lo P + dbN h P - P.slt) (n := P.slt) (by omega) (by omega))
      (by rw [hg.addr (by omega), hg.addr (by omega)]; exact Geo.sep (by omega) (by omega) (by omega)) (by omega)
      (f := fun τ i => dbF h P τ (dbN h P - P.slt + i))
      (Inv := fun τ m => (K2 h P τ m ∧ P.any = 0) ∧
        (∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0) ∧
        YZ P.scr (8 + h.D + P.slt) m) fun τ m m' ⟨⟨hk, ha'⟩, h1, h2⟩ hf' => ?_).mono
      (fun τ s ⟨⟨⟨hc, hk, hy⟩, r0, r1, lr, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi => hy i (by omega), fun i hi => ?_⟩, r0, r1, lr,
        fun i hi => ?_⟩) fun τ s ⟨hc, ⟨hk, h1, h2⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
    · rw [hg.addr (by omega)] at hf'
      refine ⟨⟨K2.keep h hk hf' fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega) (by omega), ha'⟩,
        sbytes_keep hf' (fun r hr => ?_) (by omega) h1, sbytes_keep hf' (fun r hr => ?_) (by omega) h2⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega) (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega) (by omega) (by omega)
    · rw [show oY + (8 + h.D + P.slt) + i = oY + (8 + h.D + P.slt + i) by omega, hy _ (by omega),
        getD_ge (by simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]; omega)]
    · rw [hg.byteAt_scr (by omega), show oEm + lo P + dbN h P - P.slt + i = oEm + lo P + (dbN h P - P.slt + i) by omega]
      exact hk.1.2.2.2.1 _ (by omega)
    · have hl : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
        simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]
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
theorem lenF_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Yf h P τ s.mem) (.block (lenSet h.H 7))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Mf h P) (nbF h P) τ s.mem ∧ Yf h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, ⟨hk, ha⟩, hy⟩ => ?_
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hL := h.L_le
  have hB := h.B_ge
  have hsl := hk.1.slt32
  obtain ⟨hlo, hdb, hsum, hK, hD', hD0, hK0⟩ := fitB h hk.1 hk.2.1
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  obtain ⟨a7, r7, v7⟩ := argAt hk.1 hc.st (j := 7) (by decide)
  replace v7 : s.mem.readW ((P.lay h.D).fr (arg 7)) 32 = BitVec.ofNat 32 P.slt := v7
  have e1 : BitVec.ofNat 32 (P.slt + (8 + h.D) + h.L) >>> lgB h.H = BitVec.ofNat 32 ((P.slt + (8 + h.D) + h.L) / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by omega), h.pow_lg]
  have hw : WP isa (.block (lenSet h.H 7)) s fun t =>
      t.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (P.slt + (8 + h.D)))).writeW ((P.lay h.D).fr sNb)
        (BitVec.ofNat 32 (nbF h P)) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [lenSet, sp0, ld, st, mw, hc.st.sp, a7, r7, v7, arg_lt, slotAt hk.1 (d := sL) (by decide),
      slotAt hk.1 (d := sNb) (by decide), hc.st.inFr (d := sL) (n := 4) (by show sL + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sNb) (n := 4) (by show sNb + 4 ≤ frameBytes; decide),
      movw_val (show 8 + dig h.H < 2 ^ 16 by show 8 + h.D < 2 ^ 16; omega),
      movw_val (show lenL h.H < 2 ^ 16 by show h.L < 2 ^ 16; omega), BitVec.ofNat_add_ofNat, e1, h.lg_range,
      VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨K2.keep h hk fr fun r hr => ?_, ?_, ?_⟩,
    sbytes_keep fr (fun r hr => ?_) (by decide) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Mf_length]
  · rw [m, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok (by decide) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by decide) (by rw [hg.F]; decide)).symm

/-- A salt of the expected length. -/
theorem fixed_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ P.any = 0) (fixedPath h.H)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (Mf h P τ) then 1 else 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P ∧ P.any = 0
  swap
  · exact VP.empty fun σ s h' => hf ⟨h'.2.1.2.1, h'.2.2⟩
  obtain ⟨hf, ha⟩ := hf
  have hg := hi₀.geo
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
  show VP _ (.seq (yDig h.H 4) (.seq (.block (fxSalt h.H)) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (lenSet h.H 7)) (.seq (ctHash h.H) (cmpH h.H)))))) _
  refine (yDig_vf h P ⟨σ₀, hi₀⟩ (P.any = 0)).seq ?_
  refine VP.assoc ((fxSalt_vp h P ⟨σ₀, hi₀⟩).seq ((lenF_vp h P ⟨σ₀, hi₀⟩).seq ?_))
  exact (tail_vp h P ⟨σ₀, hi₀⟩ hT (Nat.succ_pos _) (msg := Mf h P) fun τ => by
      rw [Mf_length]; show _ ≤ ((P.slt + (8 + h.D) + h.L) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega).mono
    (fun τ s ⟨hc, hk, hy⟩ => ⟨hc, hk, fun i hi => hy i (by omega)⟩) fun τ s ⟨hc, hk, r0⟩ => ⟨hc, hk, r0⟩

end VG.Proof.RsaPss.Arm.Vf
