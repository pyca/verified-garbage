module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.Chk
public import VerifiedGarbage.Proof.RsaOaep.X86.MgfSlots
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaOaep.X86.Label
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtBase
import VerifiedGarbage.Proof.RsaPss.X86.CtMgf
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP decryption on x86: `EM` unmasked

As on ARMv7 (`Proof/RsaOaep/Arm/DecUnmask.lean`): the label's hash to
`scratch + oLh` (`label_vp`), then the seed unmasked with MGF1 of
`maskedDB` and `DB` with MGF1 of the seed, in place (`mgf_vp`, with the
slots `seedArgs` and `dbArgs` set): `EM`'s place holds `V5`, `EM` unmasked
as `Proof.RsaOaep.chain_eq` states it (`unmask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes oRsa oEm oSt oCW arg ld st mi atS addi sCtr sDone)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

variable (h g : OHash)

/-- What the decoding keeps: the result's slot, and that `k` is long enough. -/
abbrev K0 (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ 2 * h.H.D + 2 ≤ P.K ∧ m.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ

/-- `lHash`, and where it is. -/
abbrev lhB (P : EP) (σ : State) : List Byte := h.G.hash (labB P σ)
abbrev LH (P : EP) (σ : State) (m : Mem) : Prop := ∀ i < h.H.D, m (sa P.scr (oLh + i)) = (lhB h P σ).getD i 0

/-- `EM`'s place holds `f`. -/
abbrev EMv (P : EP) (m : Mem) (f : Nat → Byte) : Prop := ∀ x < P.K, m (sa P.scr (oEm + x)) = f x

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

theorem EMv.keep {f : Nat → Byte} (he : EMv P m f) (hf : Frame rs m m') (hK : P.K ≤ 1024)
    (hd : ∀ r ∈ rs, (sR P.scr oEm P.K).Disjoint r) : EMv P m' f :=
  sbytes_keep hf hd (by oomega) he

end keep

/-! ## The label's hash -/

/-- After the label's hash. -/
abbrev U1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ (K0 h P σ s.mem ∧ EMv P s.mem (V P σ)) ∧ LH h P σ s.mem

theorem lab_vp (P : EP) :
    VP (fun σ s => C2 h.H.D P σ s ∧ isa.eval .b s = some false) (hashLabel h.H 17 oLh) (U1 h P) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.D_le
  have hl := ok.fits P.LAB (by simp)
  simp only [BitVec.toNat_setWidth] at hl
  rw [Nat.mod_eq_of_lt (by have := P.lab.isLt; omega)] at hl
  have hlab : RBuf P.lay P.lab P.ll := ⟨hl, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  have dS : ∀ {o n : Nat}, o + n ≤ oRsa → Region.Disjoint ⟨P.lab.setWidth 64, P.ll⟩ (sR P.scr o n) :=
    fun hon => (hg.ro ok hon (R := P.LAB) (by simp)).symm
  refine (label_vp hg h (j := 17) (o := oLh) (ll := P.ll) (lab := P.lab) (by simp) updLab17_taint finLab17_taint
    rfl rfl hlab (dS (by oomega)) (dS (by oomega)) (ok.low_buf (R := P.LAB) (.inl (by simp))).symm (by oomega)
    (by oomega) (labB := labB P) (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := fun σ m => K0 h P σ m ∧ EMv P m (V P σ)) ?_).mono
    (fun σ s ⟨⟨hc, hi, he, hr, hk, cf⟩, e⟩ => ⟨hc, ⟨hi, ?_, hr, hk⟩, he⟩) fun σ s hh => hh
  · intro σ m m' ⟨hk, he⟩ hf
    refine ⟨hk.keep h hf fun r hr => ?_, he.keep hf hK fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
      · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
      · exact Lay.fr_low (by oomega) (by show (3448 : Nat) ≤ 2 ^ 32; decide)
      · exact hg.slot ok (by oomega) (by rw [hg.F]; decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
      · exact hg.low ok (by oomega)
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · by_contra hf
    simp only [eval, cf, decide_eq_true (show P.K < 2 * h.H.D + 2 by omega)] at e
    exact absurd e (by decide)

/-! ## The seed -/

/-- What unmasking keeps: `K0`, `lHash` and `EM`'s first byte. -/
abbrev X1 (P : EP) (σ : State) (m : Mem) : Prop := K0 h P σ m ∧ LH h P σ m ∧ m (sa P.scr (oEm + 0)) = V P σ 0

theorem x1_keep {P : EP} (hg : Geo P.lay P.scr) {dOff dl : Nat} (hfd : dOff + dl ≤ oBuf) (h0 : oEm + 1 ≤ dOff) :
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
    exact hf _ fun r hr => mgfW_byte g hg hfd (o := oEm + 0) (by oomega) (by oomega) (by omega) r hr _
      (Region.contains_self _ _)

/-- Four slots written, and the memory around them. -/
theorem slots4 {L : Lay} {scr : BitVec 32} {σ s t : State} (hc : Ctx L scr σ s) (hg : Geo L scr)
    {v1 v2 v3 v4 : BitVec 32}
    (m : t.mem = (((s.mem.writeW (L.fr sDst) v1).writeW (L.fr sDstLen) v2).writeW (L.fr sSrc) v3).writeW
      (L.fr sSrcLen) v4)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.gpr .esp = s.gpr .esp) (bp : t.gpr .ebp = s.gpr .ebp) :
    Ctx L scr σ t ∧ Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] s.mem t.mem ∧
      t.mem.readW (L.fr sSrc) 32 = v3 ∧ t.mem.readW (L.fr sSrcLen) 32 = v4 ∧
      t.mem.readW (L.fr sDst) 32 = v1 ∧ t.mem.readW (L.fr sDstLen) 32 = v2 := by
  have fr : Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  refine ⟨hc.write fr (fun r hr => ?_) rd wr sp bp, fr, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · rw [m, Lay.readW_fr_other (d := sSrc) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDst) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDst) (e := sDstLen) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, Lay.readW_fr_other (d := sDstLen) (e := sSrcLen) _ _ _ (by decide) (by decide) (by decide),
      Lay.readW_fr_other (d := sDstLen) (e := sSrc) _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]

/-- The slots' frame misses our part of `scratch`. -/
theorem slots4_dis {L : Lay} {scr : BitVec 32} (hg : Geo L scr) :
    ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen],
      (sR scr o n).Disjoint r := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro o n hon r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm

theorem x1_keep4 {P : EP} (hg : Geo P.lay P.scr) {σ : State} {m m' : Mem}
    (hf : Frame [slotR P.lay sDst, slotR P.lay sDstLen, slotR P.lay sSrc, slotR P.lay sSrcLen] m m')
    (hx : X1 h P σ m) : X1 h P σ m' := by
  have := h.D_le
  refine ⟨hx.1.keep h hf fun r hr => ?_, hx.2.1.keep h hf (slots4_dis hg _ _ (by oomega)), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [← hx.2.2]
    exact sbytes_keep (o := oEm) (n := 1) hf (slots4_dis hg _ _ (by oomega)) (by oomega)
      (f := fun _ => m (sa P.scr (oEm + 0))) (fun i hi => by rw [show i = 0 by omega]) 0 (by decide)

/-- `k - hLen - 1`, from argument 4. -/
theorem kd_eq {P : EP} {σ : State} {m : Mem} (hk : K0 h P σ m) :
    BitVec.ofNat 32 P.K - BitVec.ofNat 32 (h.H.D + 1) = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
  rw [sub_ofNat (by have := hk.2.1; omega), Nat.sub_add_eq]

/-- The slots for unmasking the seed with MGF1 of `maskedDB`. -/
theorem seed_vp (P : EP) :
    VP (U1 h P) (.block (seedArgs h.H 4))
      (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = V P σ (1 + i)) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)).getD i 0) := by
  refine VP.taint [.esp, .ebp] h.certs.seedArgs4 (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hk, he⟩, hl⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hk.2.1
  simp only [seedArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine wp_movi fun t4 u4 => (c3.upd u4 (by decide) (by decide)).wp_st hg (by decide) fun t5 c5 m5 => ?_
  refine wp_mov fun t6 u6 => wp_addi fun t7 u7 => ?_
  refine ((c5.upd u6 (by decide) (by decide)).upd u7 (by decide) (by decide)).wp_st hg (by decide) fun t8 c8 m8 => ?_
  refine c8.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t9 c9 u9 => ?_
  refine wp_subi fun t10 u10 _ _ => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  have e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by rw [u2.gpr, u1.gpr, hc.ebp]
  have e7 : t7.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by
    rw [u7.gpr, u6.gpr, m5.gpr, u4.other _ (by decide), m3.gpr, u2.other _ (by decide), u1.other _ (by decide),
      hc.ebp]
  have e10 : t10.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u10.gpr, u9.gpr]; exact kd_eq h hk
  have m11 : t11.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW
      (P.lay.fr sDstLen) (BitVec.ofNat 32 h.H.D)).writeW (P.lay.fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW (P.lay.fr sSrcLen)
          (BitVec.ofNat 32 (P.K - h.H.D - 1)) := by
    rw [m11.mem, e10, u10.mem, u9.mem, m8.mem, e7, u7.mem, u6.mem, m5.mem, u4.gpr, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  have dis := slots4_dis hg
  refine ⟨c, ⟨x1_keep4 h hg fr ⟨hk, hl, he 0 (by omega)⟩, r1, r2, r3, r4⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · rw [← he (1 + i) (by omega), show oEm + (1 + i) = oEm + 1 + i by omega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1) (n := h.H.D)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + i))) (fun _ _ => rfl) i hi'
  · rw [srcB_getD _ _ hi', ← he (1 + h.H.D + i) (by omega), show oEm + (1 + h.H.D + i) = oEm + 1 + h.H.D + i by omega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) (o := oEm + 1 + h.H.D) (n := P.K - h.H.D - 1)
      (f := fun i => s.mem (sa P.scr (oEm + 1 + h.H.D + i))) (fun _ _ => rfl) i hi'

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
  refine VP.taint [.esp, .ebp] h.certs.dbArgs4 (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, ⟨hx, _⟩, hsd, hdb⟩ => ?_
  have hk := hx.1
  have hi := hk.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hk.2.1
  simp only [dbArgs, atS, addi, ld, st, mi, List.cons_append, List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  refine ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).wp_st hg (by decide) fun t3 c3 m3 => ?_
  refine c3.wp_arg hg (dec_arg (j := 4) (by decide)) (by decide) (by decide) fun t4 c4 u4 => ?_
  refine wp_subi fun t5 u5 _ _ => (c4.upd u5 (by decide) (by decide)).wp_st hg (by decide) fun t6 c6 m6 => ?_
  refine wp_mov fun t7 u7 => wp_addi fun t8 u8 => ?_
  refine ((c6.upd u7 (by decide) (by decide)).upd u8 (by decide) (by decide)).wp_st hg (by decide) fun t9 c9 m9 => ?_
  refine wp_movi fun t10 u10 => (c9.upd u10 (by decide) (by decide)).wp_st hg (by decide) fun t11 c11 m11 =>
    WP.block_nil ?_
  have e2 : t2.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) := by rw [u2.gpr, u1.gpr, hc.ebp]
  have e5 : t5.gpr .eax = BitVec.ofNat 32 (P.K - h.H.D - 1) := by
    rw [u5.gpr, u4.gpr]; exact kd_eq h hk
  have e8 : t8.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + 1) := by
    rw [u8.gpr, u7.gpr, m6.gpr, u5.other _ (by decide), u4.other _ (by decide), m3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), hc.ebp]
  have m11 : t11.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW
      (P.lay.fr sDstLen) (BitVec.ofNat 32 (P.K - h.H.D - 1))).writeW (P.lay.fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW (P.lay.fr sSrcLen) (BitVec.ofNat 32 h.H.D) := by
    rw [m11.mem, u10.gpr, u10.mem, m9.mem, e8, u8.mem, u7.mem, m6.mem, e5, u5.mem, u4.mem, m3.mem, e2, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 hc hg m11 (by rw [c11.st.rd, hc.st.rd]) (by rw [c11.st.wr, hc.st.wr])
    (by rw [c11.st.sp, hc.st.sp]) (by rw [c11.ebp, hc.ebp])
  have dis := slots4_dis hg
  refine ⟨c, ⟨x1_keep4 h hg fr hx, r1, r2, r3, r4⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · rw [V3, mix_out (by omega), sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hdb i hi', srcB_getD _ _ hi']
  · rw [srcB_getD _ _ hi', V3, mix_in (by omega) (by omega), show 1 + i - 1 = i by omega]
    exact sbytes_keep fr (dis _ _ (by oomega)) (by oomega) hsd i hi'

/-! ## Unmasking -/

/-- After unmasking: `EM`'s place holds `V5`. -/
abbrev U5 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ X1 h P σ s.mem ∧ EMv P s.mem (V5 h g P σ)

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
    (by omega) hD0 (by oomega) (by oomega) (by oomega) (by oomega) (.inr (Nat.le_refl _))
    (seed := fun σ => srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)) (fun σ => srcB_length _ _ _)
    (x1_keep h g hg (by oomega) (by oomega))
  have P2 := mpOf g hg (so := oEm + 1) (sl := h.H.D) (dOff := oEm + 1 + h.H.D) (dl := P.K - h.H.D - 1) hD0
    (by omega) (by oomega) (by oomega) (by oomega) (by oomega) (.inl (Nat.le_refl _))
    (seed := fun σ => srcB (V3 h g P σ) 1 h.H.D) (fun σ => srcB_length _ _ _) (x1_keep h g hg (by oomega) (by oomega))
  refine VP.seq (seed_vp h P) (VP.seq (mgf_vp g P1 (dstv := fun σ i => V P σ (1 + i)))
    (VP.seq (db_vp h g P) ((mgf_vp g P2 (dstv := fun σ i => V3 h g P σ (1 + h.H.D + i))).mono
      (fun _ _ hh => hh) fun σ s ⟨hc, ⟨hx, _⟩, hdb, hsd⟩ => ⟨hc, hx, fun x hx' => ?_⟩)))
  by_cases h0 : x = 0
  · subst h0
    rw [hx.2.2, V5, mix_out (by omega), V3, mix_out (by omega)]
  by_cases h1 : x < 1 + h.H.D
  · have e := hsd (x - 1) (by omega)
    rw [show oEm + 1 + (x - 1) = oEm + x by omega, srcB_getD _ _ (by omega), show 1 + (x - 1) = x by omega] at e
    rw [e, V5, mix_out (by omega)]
  · have e := hdb (x - 1 - h.H.D) (by omega)
    rw [show oEm + 1 + h.H.D + (x - 1 - h.H.D) = oEm + x by omega,
      show 1 + h.H.D + (x - 1 - h.H.D) = x by omega] at e
    rw [e, V5, mix_in (by omega) (by omega), show x - (1 + h.H.D) = x - 1 - h.H.D by omega]

end VG.Proof.RsaOaep.X86.Dec
