module

public import VerifiedGarbage.Proof.RsaPss.X86.SgEnc2
public import VerifiedGarbage.Proof.RsaOaep.X86.MgfSlots
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSASSA-PSS signing on x86: `maskedDB`

`DB ⊕= MGF1(H, dbLen)` (`mask_vp`): MGF1's slots (`margs_vp`), then
RSAES-OAEP's MGF1 with the hash function `g` of the table `mgf1`
(`Proof.RsaOaep.X86.mgf_vp`); and `maskedDB`'s first byte ANDed with the
mask `c` (`top_vp`): `EM` is `emT` of the specification's encoding
(`EncBytes.lean`), and so is the whole encoding (`enc_vp`), whose stages
keep the addresses of the statics (`VP.syms`) for the indirect calls.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaOaep.X86 (Fns sSrc sSrcLen sDst sDstLen sTab sHl)
open VG.Proof.RsaOaep.X86 (OHash TabFacts MP mpOf Sl VP.syms)

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

variable (h : PssHash)

/-- `EM`'s bytes outside `DB` and `H`: the leading zero and `0xbc`. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ (∀ i < lo P, m (sa P.scr (oEm + i)) = 0) ∧ m (sa P.scr (oEm + (P.K - 1))) = 0xbc

/-- The mask, with MGF1's hash function `G`. -/
abbrev mkS (G : Spec.Mgf1.Hash) (P : EP) (σ : State) : List Byte := Spec.Mgf1.mgf1 G (Hs h P σ) (dbN h P)

theorem Hs_length (P : EP) (σ : State) : (Hs h P σ).length = h.D := by
  rw [Hs, ← h.hash]; have := (PssHash.valid h).2 (Mp h P σ); rw [this, h.glen]

/-- MGF1's slots: `H` its source, `DB` its destination. -/
abbrev Ms (P : EP) (m : Mem) : Prop :=
  Sl (P.lay h.D) P.scr (oEm + lo P + dbN h P) h.D (oEm + lo P) (dbN h P) m

/-- MGF1's slots, from those of the parameters; `DB` and `H` from `EM`. -/
theorem margs_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) (.block (mgfArgsT h.H))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ (Ko h P σ s.mem ∧ Ms h P s.mem) ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  refine VP.taint [.esp, .ebp] h.certs.mgfArgs (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, he⟩ => ?_
  simp only [mgfArgsT, atDb, atS, addSlot, addi, ld, st, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append,
    List.nil_append]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  have c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
  refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
    (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => ?_
  refine (c2.upd u3 (by decide) (by decide)).wp_st hg (by decide) fun t4 c4 m4 => ?_
  refine c4.wp_slot hg (by decide) (by decide) (by decide) fun t5 c5 u5 => ?_
  refine c5.wp_st hg (by decide) fun t6 c6 m6 => wp_add fun t7 u7 _ => ?_
  refine (c6.upd u7 (by decide) (by decide)).wp_st hg (by decide) fun t8 c8 m8 => wp_movi fun t9 u9 => ?_
  refine (c8.upd u9 (by decide) (by decide)).wp_st hg (by decide) fun t10 c10 m10 => WP.block_nil ?_
  have e3 : t3.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + lo P) := by
    rw [u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aFr ok sLo (by decide), hk.1.2.2.2.1, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  have e5 : t5.gpr .ecx = BitVec.ofNat 32 (dbN h P) := by
    rw [u5.gpr, m4.mem, Lay.readW_fr_other (d := sDb) (e := sDst) _ _ _ (by decide) (by decide) (by decide), u3.mem,
      u2.mem, u1.mem, hk.1.2.2.2.2]
  have e7 : t7.gpr .eax = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) := by
    rw [u7.gpr, m6.gpr, u5.other _ (by decide), m4.gpr, e3, e5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have m10 : t10.mem = (((s.mem.writeW ((P.lay h.D).fr sDst) (P.scr + BitVec.ofNat 32 (oEm + lo P))).writeW
      ((P.lay h.D).fr sDstLen) (BitVec.ofNat 32 (dbN h P))).writeW ((P.lay h.D).fr sSrc)
        (P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P))).writeW ((P.lay h.D).fr sSrcLen) (BitVec.ofNat 32 h.D) := by
    rw [m10.mem, u9.gpr, u9.mem, m8.mem, e7, u7.mem, m6.mem, e5, u5.mem, m4.mem, e3, u3.mem, u2.mem, u1.mem]
  obtain ⟨c, fr, r1, r2, r3, r4⟩ := slots4 hc hg m10 (by rw [c10.st.rd, hc.st.rd]) (by rw [c10.st.wr, hc.st.wr])
    (by rw [c10.st.sp, hc.st.sp]) (by rw [c10.ebp, hc.ebp])
  have dis := slots4_dis hg
  have kp := hk.1.keep h fr fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact away3_slot (by decide) (.inr (by decide))
  have he' : ∀ i < P.K, t10.mem (sa P.scr (oEm + i)) = emC h P σ i := fun i hi =>
    by rw [sbytes_keep (o := oEm) (n := P.K) fr (dis _ _ (by omega)) (by omega) he i hi]
  refine ⟨c, ⟨⟨kp, fun i hi => ?_, ?_⟩, r1, r2, r3, r4⟩, fun i hi => ?_, fun i hi => ?_⟩
  · rw [he' i (by omega)]
    unfold emC emB emA
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left hi]
  · rw [he' _ (by omega)]
    exact ite_eq_left rfl
  · rw [Nat.add_assoc, he' _ (by omega)]
    unfold emC emB emA
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  · rw [Nat.add_assoc, Nat.add_assoc, he' _ (by omega)]
    unfold emC emB
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega

/-- `maskedDB`, before its first byte's top bits are cleared: MGF1 with the
hash function `g` of the table at the argument 23. -/
theorem mask_vp (P : EP) (hP : ∃ σ, In h.D P σ) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) ∧ s.syms = σ.syms)
      (.seq (.block (mgfArgsT h.H)) (Impl.RsaOaep.X86.mgfXor fG 23))
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h g.G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧ s.syms = σ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hD0 : 0 < h.D := h.D_pos
  have hS := g.S_le
  have hW := g.Wb_le
  have hF := g.F_le
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  have hC : (P.lay h.D).C ≤ 2 ^ 32 := by have := ok.BC; have := (P.lay h.D).B.isLt; omega
  have e4 : Impl.RsaOaep.X86.oCtr = 768 := rfl
  have e5 : Impl.RsaOaep.X86.oBuf = 2048 := rfl
  -- What `mgfXor` writes misses the parameters and the bytes of `EM` outside `DB` and `H`.
  have away : ∀ r ∈ Proof.RsaOaep.X86.mgfW g (P.lay h.D) P.scr (oEm + lo P) (dbN h P), Away3 (P.lay h.D) r ∧
      ∀ i, (i < lo P ∨ i = P.K - 1) → ¬ r.Contains (sa P.scr (oEm + i)) 1 := by
    intro r hr
    simp only [Proof.RsaOaep.X86.mgfW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨away3_scr hg (by pomega), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega)
        (by pomega) (by pomega) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega)
        (by pomega) (by pomega) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega)
        (by pomega) (by pomega) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega)
        (by pomega) (by pomega) _ (Region.contains_self _ _)⟩
    · exact ⟨⟨Lay.fr_low (by decide) hC, Lay.fr_low (by decide) hC, Lay.fr_low (by decide) hC⟩,
        fun i hi => hg.low ok (o := oEm + i) (n := 1) (by pomega) _ (Region.contains_self _ _)⟩
    · exact ⟨away3_scr hg (by pomega), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by pomega)
        (by pomega) (by pomega) _ (Region.contains_self _ _)⟩
    all_goals exact ⟨away3_slot (by decide) (.inr (by decide)), fun i hi => (hg.slot ok (o := oEm + i) (n := 1)
      (by pomega) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)⟩
  have hX : ∀ σ m m', Ko h P σ m → Frame (Proof.RsaOaep.X86.mgfW g (P.lay h.D) P.scr (oEm + lo P) (dbN h P)) m m' → Ko h P σ m' :=
    fun σ m m' ⟨hk, h0, hbc⟩ hf' => ⟨hk.keep h hf' fun r hr => (away r hr).1, fun i hi => by
      rw [← h0 i hi]; exact hf' _ fun r hr => (away r hr).2 i (.inl hi),
      by rw [← hbc]; exact hf' _ fun r hr => (away r hr).2 _ (.inr rfl)⟩
  have mp := mpOf g hg (so := oEm + lo P + dbN h P) (sl := h.D) (dOff := oEm + lo P) (dl := dbN h P) hD0
    (by omega) (by omega) (by omega) (by pomega) (by pomega) (.inr (Nat.le_refl _)) (seed := Hs h P)
    (fun σ => Hs_length h P σ) hX (sg_arg h (j := 23) (by decide)) hi₀.tbl Proof.RsaOaep.X86.tabArg23_taint
    (fun σ m hk => hT σ hk.1.1.tabT) fne
  exact VP.seq (VP.syms (margs_vp h P ⟨σ₀, hi₀⟩)) ((Proof.RsaOaep.X86.mgf_vp g mp (dstv := dbv h P)).mono (fun _ _ h => h)
    fun σ s ⟨⟨hc, ⟨hk, _⟩, hd, hh⟩, sy⟩ => ⟨⟨hc, hk, hd, hh⟩, sy⟩)

/-- `EM`, as the specification encodes it (`RsaPss.emT`). -/
abbrev emF (G : Spec.Mgf1.Hash) (P : EP) (σ : State) (i : Nat) : Byte :=
  RsaPss.emT (lo P) (dbN h P) P.sl (saltB P σ) (Hs h P σ) (mkS h G P σ) ((cW (xB P)).setWidth 8) i

theorem andByte (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 := by
  have e1 : (b.setWidth 32).setWidth 8 = b := by simp
  rw [BitVec.setWidth_and, e1]

/-- `maskedDB`'s first byte ANDed with the mask: `EM`. -/
theorem top_vp (G : Spec.Mgf1.Hash) (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0)
      (.seq (.block topSet) (.block topAnd))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h G P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  have hK := hi₀.k1024
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 (oEm + lo P))
    (VP.taint [.esp, .ebp] topSet_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hk, hd, hh⟩ => ?_)
    (VP.taint _ topAnd_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, hd, hh⟩, si⟩ => ?_)
  · simp only [topSet, atDb, atS, addSlot, addi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
    have c2 : Ctx (P.lay h.D) P.scr σ t2 := (hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)
    refine wp_addm (B := (P.lay h.D).B) (by rw [c2.st.sp])
      (by rw [hg.aFr ok sLo (by decide)]; exact c2.rFr hg sLo (by decide)) fun t3 u3 => WP.block_nil ?_
    have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    refine ⟨⟨c2.upd u3 (by decide) (by decide), m3 ▸ hk, m3 ▸ hd, m3 ▸ hh⟩, ?_⟩
    rw [u3.gpr, u2.gpr, u1.gpr, u2.mem, u1.mem, hc.ebp, hg.aFr ok sLo (by decide), hk.1.2.2.2.1, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · have ad : addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) 0 = sa P.scr (oEm + lo P) := by
      rw [hg.addrD (by omega), Nat.add_zero]
    have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega)
    simp only [topAnd, Impl.RsaPkcs1Sig.X86.at_, Impl.RsaPkcs1Sig.X86.stk]
    refine wp_movzx8 (a := sa P.scr (oEm + lo P)) (by rw [ea_at, si]; exact ad) rd fun t1 u1 => ?_
    have c1 : Ctx (P.lay h.D) P.scr σ t1 := hc.upd u1 (by decide) (by decide)
    have rC := c1.rFr hg sC (by decide)
    refine wp_andS (readSrc_mem (B := (P.lay h.D).B) (by rw [c1.st.sp]) (by rw [hg.aFr ok sC (by decide)]; exact rC))
      fun t2 u2 => ?_
    have a2 : t2.ea ⟨.esi, 0⟩ = sa P.scr (oEm + lo P) := by
      rw [ea_at, u2.other .esi (by decide), u1.other .esi (by decide), si]; exact ad
    refine wp_store8 (a := sa P.scr (oEm + lo P)) a2 (by rw [u2.wr, u1.wr]; exact wd) fun t3 u3 => WP.block_nil ?_
    have m3 : t3.mem = s.mem.writeW (sa P.scr (oEm + lo P)) (s.mem (sa P.scr (oEm + lo P)) &&& (cW (xB P)).setWidth 8) := by
      rw [u3.mem, Reg8.reg, u2.gpr, u2.mem, u1.gpr, u1.mem, hg.aFr ok sC (by decide), hk.1.2.2.1, andByte]
    have fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t3.mem := by
      rw [m3]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    refine ⟨(c1.upd u2 (by decide) (by decide)).write (by rw [u2.mem, u1.mem]; exact fr) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)) u3.rd u3.wr (by rw [u3.gpr])
        (by rw [u3.gpr]), hk.1.keep h fr fun r hr => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by omega)
    rw [m3, sa_write P.scr _ _ (by omega) (by omega)]
    have hl := Hs_length h P σ
    unfold emF RsaPss.emT
    by_cases h1 : i < lo P
    · rw [ite_eq_right (by omega), ite_eq_left h1]; exact hk.2.1 i h1
    rw [ite_eq_right h1]
    by_cases h2 : i - lo P < dbN h P
    · rw [ite_eq_left h2]
      by_cases h3 : i - lo P = 0
      · rw [ite_eq_left (by omega), ite_eq_left h3, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega), h3]
      · rw [ite_eq_right (by omega), ite_eq_right h3, show oEm + i = oEm + lo P + (i - lo P) by omega, hd _ h2]
    rw [ite_eq_right h2, ite_eq_right (by omega)]
    by_cases h4 : i - lo P < dbN h P + (Hs h P σ).length
    · rw [ite_eq_left h4, show oEm + i = oEm + lo P + dbN h P + (i - lo P - dbN h P) by omega, hh _ (by omega)]
    · rw [ite_eq_right h4, show oEm + i = oEm + (P.K - 1) by omega]; exact hk.2.2

/-- The encoding, when everything fits, with the hash function of the table
of `MdHash` at the argument 22 and MGF1's of the table of `Hash` at 23. -/
theorem enc_vp (P : EP) (hP : ∃ σ, In h.D P σ) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VP (fun σ s => E0 h P σ s ∧ s.syms = σ.syms) (signEncT f h.H fG)
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h g.G P σ)) ∧ s.syms = σ.syms) := by
  show VP _ (.seq (yDig h.H 16) (.seq (.block (cpSalt h.H)) (.seq (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
    (.seq (.block (lenArgs h.H 19)) (.seq (ctHashT f h.H 22) (.seq (.block clrEm) (.seq zeroLoop
    (.seq (.block oneSet) (.seq (.block put1) (.seq (.ite .e (.block []) Impl.Bignum.X86.copyBytes)
    (.seq (.block (putH h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq (.block bcSet) (.seq (.block putBc)
    (.seq (.block (mgfArgsT h.H)) (.seq (Impl.RsaOaep.X86.mgfXor fG 23) (.seq (.block topSet) (.block topAnd)))))))))))))))))) _
  exact (VP.syms (yDig_sg h P hP)).seq (vpAssoc ((VP.syms (salt_vp h P hP)).seq ((VP.syms (lenSet_vp h P)).seq
    ((hash_vp h P hP hTH fneH).seq (vpAssoc ((VP.syms (clr_vp h P hP)).seq (vpAssoc ((VP.syms (one_vp h P hP)).seq
    ((VP.syms (cpS_vp h P hP)).seq (vpAssoc ((VP.syms (putH_vp h P hP)).seq (vpAssoc ((VP.syms (bc_vp h P hP)).seq
    (vpAssoc ((mask_vp h P hP g hT fne).seq (VP.syms (top_vp h g.G P hP)))))))))))))))))

end VG.Proof.RsaPss.X86.Sg
