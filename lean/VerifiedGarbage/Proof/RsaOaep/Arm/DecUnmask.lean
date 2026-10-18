module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncMask
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm

/-!
# RSAES-OAEP decryption on ARMv7: `EM` unmasked

The label's hash to `scratch + oLh` (`label_vp`), then the seed unmasked
with MGF1 of `maskedDB` and `DB` with MGF1 of the seed, in place (`mgf_vp`,
with the slots `seedArgs` and `dbArgs` set): `EM`'s place holds `V5`, `EM`
unmasked as `Proof.RsaOaep.chain_eq` states it (`unmask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sCtr sDone)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaOaep.Arm.Enc (Sl mpOf mgfW_slot mgfW_byte)

variable (h g : OHash)

/-- What the decoding keeps: the result's slot, and that `k` is long enough. -/
abbrev K0 (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ 2 * h.H.D + 2 ≤ P.K ∧ m.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ

/-- `lHash`, and where it is. -/
abbrev lhB (P : EP) (σ : State) : List Byte := h.G.hash (labB P σ)
abbrev LH (P : EP) (σ : State) (m : Mem) : Prop := ∀ i < h.H.D, m (sa P.scr (oLh + i)) = (lhB h P σ).getD i 0

/-- The seed unmasked (`V3`), then `DB` (`V5`). -/
abbrev mk3 (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.mgf1 g.G (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)) h.H.D
abbrev V3 (P : EP) (σ : State) : Nat → Byte := mixV (V P σ) (mk3 h g P σ) 1 h.H.D
abbrev mk5 (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.mgf1 g.G (srcB (V3 h g P σ) 1 h.H.D) (P.K - h.H.D - 1)
abbrev V5 (P : EP) (σ : State) : Nat → Byte := mixV (V3 h g P σ) (mk5 h g P σ) (1 + h.H.D) (P.K - h.H.D - 1)

theorem srcB_getD (V : Nat → Byte) (a : Nat) {n i : Nat} (hi : i < n) : (srcB V a n).getD i 0 = V (a + i) :=
  Proof.RsaOaep.map_range_getD' (fun i => V (a + i)) hi

theorem srcB_length (V : Nat → Byte) (a n : Nat) : (srcB V a n).length = n := by simp [srcB]

theorem mix_in {V : Nat → Byte} {mk : List Byte} {e n o : Nat} (h₁ : e ≤ o) (h₂ : o < e + n) :
    mixV V mk e n o = V o ^^^ mk.getD (o - e) 0 := by
  simp only [mixV]; rw [ifp ⟨h₁, h₂⟩]

theorem mix_out {V : Nat → Byte} {mk : List Byte} {e n o : Nat} (h : o < e ∨ e + n ≤ o) :
    mixV V mk e n o = V o := by
  simp only [mixV]; rw [ifn (by omega)]

section keep
variable {P : EP} {σ : State} {rs : List Region} {m m' : Mem}

theorem K0.keep (hk : K0 h P σ m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotR P.lay sRes).Disjoint r) :
    K0 h P σ m' :=
  ⟨hk.1, hk.2.1, slot_keep hf hd hk.2.2.1, hk.2.2.2⟩

theorem LH.keep (hl : LH h P σ m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sR P.scr oLh h.H.D).Disjoint r) :
    LH h P σ m' :=
  sbytes_keep hf hd (by have := h.D_le; oomega) hl

end keep

/-! ## The label's hash -/

/-- After the label's hash. -/
abbrev U1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ (K0 h P σ s.mem ∧ ∀ x < P.K, s.mem (sa P.scr x) = V P σ x) ∧ LH h P σ s.mem

theorem lab_vp (P : EP) :
    VP (fun σ s => C2 h.H.D P σ s ∧ isa.eval .ne s = some false) (hashLabel h.H 17 oLh) (U1 h P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.D_le
  have hb : RBuf P.lay P.lab P.ll := by
    have hf := ok.fits P.LAB (by simp)
    simp only [Proof.X25519.Arm.addr_toNat] at hf
    exact ⟨hf, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  refine (label_vp hg h (j := 17) (o := oLh) (ll := P.ll) (lab := P.lab) (by simp) (arg_lt (by decide))
    (arg_lt (by decide)) rfl rfl hb (hg.ro ok (by oomega) (R := P.LAB) (by simp)).symm
    (hg.ro ok (by oomega) (R := P.LAB) (by simp)).symm (ok.low_buf (R := P.LAB) (.inl (by simp))).symm
    (by oomega) (by oomega) (labB := labB P) (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := fun σ m => K0 h P σ m ∧ ∀ x < P.K, m (sa P.scr x) = V P σ x) ?_).mono
    (fun σ s ⟨⟨hc, hi, he, hr, hk, z⟩, e⟩ => ⟨hc, ⟨hi, ?_, hr, hk⟩, he⟩) fun σ s hh => hh
  · intro σ m m' ⟨hk, he⟩ hf
    refine ⟨hk.keep h hf fun r hr => ?_, em_keep hf (fun r hr => ?_) (by omega) he⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
      · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
      · exact Lay.fr_low (by decide)
      · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
      · exact hg.low ok (by oomega)
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · rw [VG.Proof.X25519.Arm.eval_ne] at e
    have z' : s.z = true := by cases hz : s.z <;> simp_all
    rw [z'] at z
    exact of_decide_eq_true z.symm

/-! ## The seed -/

/-- What unmasking keeps: `K0`, `lHash` and `EM`'s first byte. -/
abbrev X1 (P : EP) (σ : State) (m : Mem) : Prop := K0 h P σ m ∧ LH h P σ m ∧ m (sa P.scr 0) = V P σ 0

theorem x1_keep {P : EP} (hg : Geo P.lay P.scr) {dOff dl : Nat} (hfd : dOff + dl ≤ oBuf) (h0 : 0 < dOff) :
    ∀ σ m m', X1 h P σ m → Frame (mgfW g P.lay P.scr dOff dl) m m' → X1 h P σ m' := by
  intro σ m m' ⟨hk, hl, h0'⟩ hf
  have := g.S_le; have := g.Wb_le; have := g.F_le; have := h.D_le
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hk.keep h hf (mgfW_slot g hg hfd (by decide) (by decide)), hl.keep h hf fun r hr => ?_, ?_⟩
  · simp only [mgfW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact hg.low ok (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
  · rw [← h0']
    have e := hf _ fun r hr => mgfW_byte g hg hfd (o := oEm + 0) (by oomega) (by oomega) r hr _
      (Region.contains_self _ _)
    simpa [sa, oEm] using e

/-- Four slots written. -/
theorem frame4 (L : Lay) (m : Mem) (a b c d : BitVec 32) :
    Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] m
      ((((m.writeW (L.fr sDst) a).writeW (L.fr sDstLen) b).writeW (L.fr sSrc) c).writeW (L.fr sSrcLen) d) :=
  (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
    ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))

theorem dis4 {P : EP} (hg : Geo P.lay P.scr) {o n : Nat} (hon : o + n ≤ oRsa) :
    ∀ r ∈ [slotR P.lay sDst, slotR P.lay sDstLen, slotR P.lay sSrc, slotR P.lay sSrcLen],
      (sR P.scr o n).Disjoint r := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm

theorem x1_keep4 {P : EP} (hg : Geo P.lay P.scr) {σ : State} {m m' : Mem}
    (hf : Frame [slotR P.lay sDst, slotR P.lay sDstLen, slotR P.lay sSrc, slotR P.lay sSrcLen] m m')
    (hx : X1 h P σ m) : X1 h P σ m' := by
  have := h.D_le
  refine ⟨hx.1.keep h hf fun r hr => ?_, hx.2.1.keep h hf (dis4 hg (by oomega)), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [← hx.2.2]
    have e := sbytes_keep (o := 0) (n := 1) hf (dis4 hg (by oomega)) (by decide)
      (f := fun _ => m (sa P.scr 0)) (fun i hi => by rw [show i = 0 by omega]) 0 (by decide)
    simpa using e

/-- The slots for unmasking the seed with MGF1 of `maskedDB`. -/
theorem seed_vp (P : EP) :
    VP (U1 h P) (.block (seedArgs h.H 4))
      (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = V P σ (1 + i)) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)).getD i 0) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hk, he⟩, hl⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hk.2.1
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  have hw : WP isa (.block (seedArgs h.H 4)) s fun t =>
      t.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW
        (P.lay.fr sDstLen) (BitVec.ofNat 32 h.H.D)).writeW (P.lay.fr sSrc)
          (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW (P.lay.fr sSrcLen)
            (BitVec.ofNat 32 (P.K - h.H.D - 1)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [seedArgs, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS, a4, r4, v4, arg_lt,
      sDst_lt, sDstLen_lt, sSrc_lt, sSrcLen_lt,
      movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show h.H.D + 1 < 2 ^ 16 by omega),
      movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega),
      Offset.ofNat_sub_ofNat (show h.H.D + 1 ≤ P.K by omega), Nat.sub_add_eq]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr := frame4 P.lay s.mem (P.scr + BitVec.ofNat 32 (oEm + 1)) (BitVec.ofNat 32 h.H.D)
    (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D)) (BitVec.ofNat 32 (P.K - h.H.D - 1))
  rw [← m] at fr
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
    ⟨x1_keep4 h hg fr ⟨hk, hl, he 0 (by omega)⟩, ?_, ?_, ?_, ?_⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · have e := em_keep fr (dis4 hg (by oomega)) (by omega) he (1 + i) (by omega)
    rwa [show oEm + 1 + i = 1 + i by oomega]
  · rw [srcB_getD _ _ hi']
    have e := em_keep fr (dis4 hg (by oomega)) (by omega) he (1 + h.H.D + i) (by omega)
    rwa [show oEm + 1 + h.H.D + i = 1 + h.H.D + i by oomega]

/-- The slots for unmasking `DB` with MGF1 of the seed. -/
theorem db_vp (P : EP) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = V P σ (1 + i) ^^^ (mk3 h g P σ).getD i 0) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)).getD i 0)
      (.block (dbArgs h.H 4))
      (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = V3 h g P σ (1 + h.H.D + i)) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (srcB (V3 h g P σ) 1 h.H.D).getD i 0) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hx, _⟩, hsd, hdb⟩ => ?_
  have hi := hx.1.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hx.1.2.1
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  have hw : WP isa (.block (dbArgs h.H 4)) s fun t =>
      t.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW
        (P.lay.fr sDstLen) (BitVec.ofNat 32 (P.K - h.H.D - 1))).writeW (P.lay.fr sSrc)
          (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW (P.lay.fr sSrcLen) (BitVec.ofNat 32 h.H.D) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [dbArgs, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS, a4, r4, v4, arg_lt,
      sDst_lt, sDstLen_lt, sSrc_lt, sSrcLen_lt,
      movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show h.H.D + 1 < 2 ^ 16 by omega),
      movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega),
      Offset.ofNat_sub_ofNat (show h.H.D + 1 ≤ P.K by omega), Nat.sub_add_eq]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr := frame4 P.lay s.mem (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D)) (BitVec.ofNat 32 (P.K - h.H.D - 1))
    (P.scr + BitVec.ofNat 32 (oEm + 1)) (BitVec.ofNat 32 h.H.D)
  rw [← m] at fr
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
    ⟨x1_keep4 h hg fr hx, ?_, ?_, ?_, ?_⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [V3, mix_out (by omega), sbytes_keep fr (dis4 hg (by oomega)) (by oomega) hdb i hi', srcB_getD _ _ hi']
  · rw [srcB_getD _ _ hi', V3, mix_in (by omega) (by omega), show 1 + i - 1 = i by omega]
    exact sbytes_keep fr (dis4 hg (by oomega)) (by oomega) hsd i hi'

/-! ## Unmasking -/

/-- After unmasking: `EM`'s place holds `V5`. -/
abbrev U5 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ X1 h P σ s.mem ∧ ∀ x < P.K, s.mem (sa P.scr x) = V5 h g P σ x

theorem unmask_vp (P : EP) :
    VP (U1 h P) (.seq (.block (seedArgs h.H 4)) (.seq (mgfXor g.H) (.seq (.block (dbArgs h.H 4)) (mgfXor g.H))))
      (U5 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1, hs.2.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have P1 := mpOf g hg (so := oEm + 1 + h.H.D) (sl := P.K - h.H.D - 1) (dOff := oEm + 1) (dl := h.H.D)
    (by omega) hD0 (by oomega) (by oomega) (.inr (Nat.le_refl _))
    (seed := fun σ => srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)) (fun σ => srcB_length _ _ _)
    (x1_keep h g hg (by oomega) (by oomega))
  have P2 := mpOf g hg (so := oEm + 1) (sl := h.H.D) (dOff := oEm + 1 + h.H.D) (dl := P.K - h.H.D - 1) hD0
    (by omega) (by oomega) (by oomega) (.inl (Nat.le_refl _)) (seed := fun σ => srcB (V3 h g P σ) 1 h.H.D)
    (fun σ => srcB_length _ _ _) (x1_keep h g hg (by oomega) (by oomega))
  refine VP.seq (seed_vp h P) (VP.seq (mgf_vp g P1 (dstv := fun σ i => V P σ (1 + i)))
    (VP.seq (db_vp h g P) ((mgf_vp g P2 (dstv := fun σ i => V3 h g P σ (1 + h.H.D + i))).mono
      (fun _ _ hh => hh) fun σ s ⟨hc, ⟨hx, _⟩, hdb, hsd⟩ => ⟨hc, hx, fun x hx' => ?_⟩)))
  by_cases h0 : x = 0
  · subst h0
    rw [hx.2.2, V5, mix_out (by omega), V3, mix_out (by omega)]
  by_cases h1 : x < 1 + h.H.D
  · have e := hsd (x - 1) (by omega)
    rw [show oEm + 1 + (x - 1) = x by oomega, srcB_getD _ _ (by omega), show 1 + (x - 1) = x by omega] at e
    rw [e, V5, mix_out (by omega)]
  · have e := hdb (x - 1 - h.H.D) (by omega)
    rw [show oEm + 1 + h.H.D + (x - 1 - h.H.D) = x by oomega, show 1 + h.H.D + (x - 1 - h.H.D) = x by omega] at e
    rw [e, V5, mix_in (by omega) (by omega), show x - (1 + h.H.D) = x - 1 - h.H.D by omega]

end VG.Proof.RsaOaep.Arm.Dec
