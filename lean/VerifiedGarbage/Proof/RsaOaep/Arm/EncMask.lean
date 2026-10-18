module

public import VerifiedGarbage.Proof.RsaOaep.Arm.EncEm
public import VerifiedGarbage.Proof.RsaOaep.Arm.MgfSlots
import all Init.Data.Nat.Bitwise.Basic

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: `EM` masked

`DB` (after the seed) masked with MGF1 of the seed, then the seed with MGF1
of the masked `DB` (`mgf_vp`, with the slots that `dbArgs` and `seedArgs`
set, `MgfSlots.lean`): `EM = Proof.RsaOaep.emOf …` (`mask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sCtr sDone)
open VG.Proof.Rsa.Arm.Recover (VP)

/-! ## The pieces -/

variable (h g : OHash)

/-- `DB` before masking. -/
abbrev dbB (P : EP) (σ : State) : List Byte :=
  lhB h P σ ++ Spec.RsaOaep.zeros (P.K - P.ml - 2 * h.H.D - 2) ++ 0x01 :: msgB P σ

/-- `DB` masked. -/
abbrev mdbB (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.xorBytes (dbB h P σ) (Spec.Mgf1.mgf1 g.G (seedB h P σ) (P.K - h.H.D - 1))

/-- What the masking keeps: `EM`'s first byte, zero. -/
abbrev X0 (P : EP) (σ : State) (m : Mem) : Prop := K0 h P σ ∧ emV P.scr m 0 = 0

theorem lhB_length (P : EP) (σ : State) : (lhB h P σ).length = h.H.D := by
  rw [lhB, h.valid.2, h.glen]

theorem seedB_length (P : EP) (σ : State) : (seedB h P σ).length = h.H.D := by simp [Spec.Rsa.bytesAt]

theorem dbB_length {P : EP} (hf : fits h P) (σ : State) : (dbB h P σ).length = P.K - h.H.D - 1 := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  simp only [dbB, List.length_append, List.length_cons, lhB_length, msgB_length, Spec.RsaOaep.zeros,
    List.length_replicate]
  omega

theorem mdbB_length {P : EP} (hf : fits h P) (σ : State) : (mdbB h g P σ).length = P.K - h.H.D - 1 := by
  rw [mdbB, Proof.Mgf1.xorBytes_length, dbB_length h hf, Proof.Mgf1.mgf1_length g.valid]; omega

theorem x0_keep {P : EP} (hg : Geo (P.lay h.H.D) P.scr) {dOff dl : Nat} (hfd : dOff + dl ≤ oBuf) (h0 : 0 < dOff) :
    ∀ σ m m', X0 h P σ m → Frame (mgfW g (P.lay h.H.D) P.scr dOff dl) m m' → X0 h P σ m' :=
  fun _ _ _ ⟨k, z⟩ hf => ⟨k, by
    rw [emV, ← z]
    exact hf _ fun r hr => mgfW_byte g hg hfd (o := oEm + 0) (by oomega) (by oomega) r hr _
      (Region.contains_self _ _)⟩

/-- The slots for masking `DB` with the seed. -/
theorem db_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml)
      (.block (dbArgs h.H 3))
      (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = (dbB h P σ).getD i 0) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
    fun σ s ⟨⟨hc, hi, hf⟩, em⟩ => ?_
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi.k1024
  have hD := h.D_le
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  obtain ⟨⟨a3, r3, v3⟩, -⟩ := argV h hi hc.st
  have hw : WP isa (.block (dbArgs h.H 3)) s fun t =>
      t.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW
        ((P.lay h.H.D).fr sDstLen) (BitVec.ofNat 32 (P.K - h.H.D - 1))).writeW ((P.lay h.H.D).fr sSrc)
          (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW ((P.lay h.H.D).fr sSrcLen) (BitVec.ofNat 32 h.H.D) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [dbArgs, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS, a3, r3, v3, arg_lt, sDst_lt, sDstLen_lt, sSrc_lt, sSrcLen_lt,
      movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show h.H.D + 1 < 2 ^ 16 by omega),
      movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega),
      Offset.ofNat_sub_ofNat (show h.H.D + 1 ≤ P.K by omega), Nat.sub_add_eq]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen, slotR (P.lay h.H.D) sSrc,
      slotR (P.lay h.H.D) sSrcLen] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  have dis : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen,
      slotR (P.lay h.H.D) sSrc, slotR (P.lay h.H.D) sSrcLen], (sR P.scr o n).Disjoint r := by
    intro o n hon r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have db := em.db (lhB_length h P σ) (msgB_length P σ) hfit
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨⟨hi, hf⟩, ?_⟩, ?_, ?_, ?_, ?_⟩,
    fun i hi' => ?_, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [emV, ← em.z0]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm) (n := 1) (f := fun _ => s.mem (sa P.scr oEm))
      (fun i hi => by rw [show i = 0 by omega, Nat.add_zero]) 0 (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [← db i hi', emV, show oEm + (1 + h.H.D + i) = oEm + 1 + h.H.D + i by oomega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1 + h.H.D) (n := P.K - h.H.D - 1)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + h.H.D + i))) (fun _ _ => rfl) i hi'
  · rw [← em.sd i hi', emV, show oEm + (1 + i) = oEm + 1 + i by oomega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1) (n := h.H.D)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + i))) (fun _ _ => rfl) i hi'

/-- The slots for masking the seed with the masked `DB`. -/
theorem seed_vp (P : EP) :
    VP (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (dbB h P σ).getD i 0 ^^^ (Spec.Mgf1.mgf1 g.G (seedB h P σ) (P.K - h.H.D - 1)).getD i 0) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0)
      (.block (seedArgs h.H 3))
      (fun σ s => Ctx (P.lay h.H.D) P.scr σ s ∧
        (X0 h P σ s.mem ∧ Sl (P.lay h.H.D) P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (seedB h P σ).getD i 0) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = (mdbB h g P σ).getD i 0) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨⟨⟨hi, hf⟩, z0⟩, _⟩, hdb, hsd⟩ => ?_
  have hg := hi.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi.k1024
  have hD := h.D_le
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  obtain ⟨⟨a3, r3, v3⟩, -⟩ := argV h hi hc.st
  have hw : WP isa (.block (seedArgs h.H 3)) s fun t =>
      t.mem = (((s.mem.writeW ((P.lay h.H.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW
        ((P.lay h.H.D).fr sDstLen) (BitVec.ofNat 32 h.H.D)).writeW ((P.lay h.H.D).fr sSrc)
          (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW ((P.lay h.H.D).fr sSrcLen)
            (BitVec.ofNat 32 (P.K - h.H.D - 1)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [seedArgs, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS, a3, r3, v3, arg_lt,
      sDst_lt, sDstLen_lt, sSrc_lt, sSrcLen_lt,
      movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show h.H.D + 1 < 2 ^ 16 by omega),
      movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega),
      Offset.ofNat_sub_ofNat (show h.H.D + 1 ≤ P.K by omega), Nat.sub_add_eq]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen, slotR (P.lay h.H.D) sSrc,
      slotR (P.lay h.H.D) sSrcLen] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  have dis : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.H.D) sDst, slotR (P.lay h.H.D) sDstLen,
      slotR (P.lay h.H.D) sSrc, slotR (P.lay h.H.D) sSrcLen], (sR P.scr o n).Disjoint r := by
    intro o n hon r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have hdl := dbB_length h hf σ
  have hml := Proof.Mgf1.mgf1_length g.valid (seedB h P σ) (P.K - h.H.D - 1)
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨⟨hi, hf⟩, ?_⟩, ?_, ?_, ?_, ?_⟩,
    sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hsd, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [emV, ← z0]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm) (n := 1) (f := fun _ => s.mem (sa P.scr oEm))
      (fun i hi => by rw [show i = 0 by omega, Nat.add_zero]) 0 (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [mdbB, Proof.Mgf1.xorBytes_getD (by omega) (by omega)]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hdb i hi'

/-- `EM` masked, byte by byte. -/
theorem emB_getD {P : EP} (hf : fits h P) (σ : State) {i : Nat} (hi : i < P.K) :
    (emB h g P σ).getD i 0 = if i = 0 then 0 else if i < 1 + h.H.D then
      (seedB h P σ).getD (i - 1) 0 ^^^ (Spec.Mgf1.mgf1 g.G (mdbB h g P σ) h.H.D).getD (i - 1) 0
      else (mdbB h g P σ).getD (i - 1 - h.H.D) 0 := by
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  have hsl := seedB_length h P σ
  have hml := Proof.Mgf1.mgf1_length g.valid (mdbB h g P σ) h.H.D
  show (0 :: (Spec.Mgf1.xorBytes (seedB h P σ) (Spec.Mgf1.mgf1 g.G (mdbB h g P σ) h.H.D) ++ mdbB h g P σ)).getD i 0 = _
  cases i with
  | zero => rfl
  | succ i =>
    rw [List.getD_cons_succ, ite_eq_right (by omega), Proof.Mgf1.getD_append, Proof.Mgf1.xorBytes_length, hsl, hml,
      Nat.min_self, Nat.add_sub_cancel]
    by_cases h1 : i < h.H.D
    · rw [ite_eq_left h1, ite_eq_left (by omega), Proof.Mgf1.xorBytes_getD (by omega) (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- `EM` masked, from `EM` before masking. -/
theorem mask_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Proof.RsaOaep.EmAt (emV P.scr s.mem) P.K h.H.D (seedB h P σ) (lhB h P σ)
        (msgB P σ) P.ml)
      (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor g.H) (.seq (.block (seedArgs h.H 3)) (mgfXor g.H))))
      (E1 h g P) := by
  by_cases hP : ∃ σ, In h.H.D P σ ∧ fits h P
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1, hs.1.2.2⟩
  obtain ⟨σ₀, hi₀, hf⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have hfit : 2 * h.H.D + 2 + P.ml ≤ P.K := hf
  have P1 := mpOf g hg (so := oEm + 1) (sl := h.H.D) (dOff := oEm + 1 + h.H.D) (dl := P.K - h.H.D - 1) hD0
    (by omega) (by oomega) (by oomega) (.inl (Nat.le_refl _)) (seed := seedB h P) (seedB_length h P)
    (x0_keep h g hg (by oomega) (by oomega))
  have P2 := mpOf g hg (so := oEm + 1 + h.H.D) (sl := P.K - h.H.D - 1) (dOff := oEm + 1) (dl := h.H.D)
    (by omega) hD0 (by oomega) (by oomega) (.inr (Nat.le_refl _)) (seed := mdbB h g P) (mdbB_length h g hf)
    (x0_keep h g hg (by oomega) (by oomega))
  refine VP.seq (db_vp h P) (VP.seq (mgf_vp g P1 (dstv := fun σ i => (dbB h P σ).getD i 0))
    (VP.seq (seed_vp h g P) ((mgf_vp g P2 (dstv := fun σ i => (seedB h P σ).getD i 0)).mono
      (fun _ _ hh => hh) fun σ s ⟨hc, ⟨⟨⟨hi, _⟩, z0⟩, _⟩, hsd, hdb⟩ => ⟨⟨hc, hi, hf⟩, fun i hi' => ?_⟩)))
  rw [emB_getD h g hf σ hi']
  by_cases h0 : i = 0
  · rw [ite_eq_left h0, h0]; exact z0
  rw [ite_eq_right h0]
  by_cases h1 : i < 1 + h.H.D
  · rw [ite_eq_left h1, emV, show oEm + i = oEm + 1 + (i - 1) by oomega]
    exact hsd _ (by omega)
  · rw [ite_eq_right h1, emV, show oEm + i = oEm + 1 + h.H.D + (i - 1 - h.H.D) by oomega]
    exact hdb _ (by omega)

end VG.Proof.RsaOaep.Arm.Enc
