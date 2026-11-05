module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc2
public import VerifiedGarbage.Proof.RsaPss.EncBytes
public import VerifiedGarbage.Proof.RsaOaep.Arm.MgfSlots
import VerifiedGarbage.Proof.Framework.Arm.Syms
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc2
meta import VerifiedGarbage.Proof.RsaPss.EncBytes
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS signing on ARMv7: `maskedDB`, and `EM`

`DB ⊕= MGF1(H, dbLen)` (`mask_vp`), `maskedDB`'s first byte ANDed with the
mask `c` (`top_vp`): `EM` is `emT` of the specification's encoding
(`EncBytes.lean`), and so is the whole encoding (`enc_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- `EM`'s bytes outside `DB` and `H`: the leading zero and `0xbc`. -/
abbrev Ko (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ (∀ i < lo P, m (sa P.scr (oEm + i)) = 0) ∧ m (sa P.scr (oEm + (P.K - 1))) = 0xbc

/-- The mask, by MGF1 with `G`. -/
abbrev mkS (G : Spec.Mgf1.Hash) (P : EP) (σ : State) : List Byte := Spec.Mgf1.mgf1 G (Hs h P σ) (dbN h P)

theorem Hs_length (P : EP) (σ : State) : (Hs h P σ).length = h.D := by
  rw [Hs, ← h.hash]; have := (PssHash.valid h).2 (Mp h P σ); rw [this, h.glen]

/-- MGF1's slots: its source `H` and its destination `DB`. -/
theorem slots_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) (.block (mgfSlots h.sh))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ (Ke h P σ s.mem ∧
        RsaOaep.Arm.Sl (P.lay h.D) P.scr (oEm + lo P + dbN h P) h.D (oEm + lo P) (dbN h P) s.mem) ∧
        EMv P s.mem (emC h P σ)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, he⟩ => ?_
  let L := P.lay h.D
  have hw : WP isa (.block (mgfSlots h.sh)) s fun t =>
      t.mem = (((s.mem.writeW (L.fr Impl.RsaOaep.Arm.sDst) (P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 (lo P))).writeW
        (L.fr Impl.RsaOaep.Arm.sDstLen) (BitVec.ofNat 32 (dbN h P))).writeW (L.fr Impl.RsaOaep.Arm.sSrc)
          (P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 (lo P) + BitVec.ofNat 32 (dbN h P))).writeW
        (L.fr Impl.RsaOaep.Arm.sSrcLen) (BitVec.ofNat 32 h.D) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [mgfSlots, atDb, atS, addSlot, sp0, ld, mw, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS,
      hk.1.2.2.2.1, hk.1.2.2.2.2, movw_val (show oEm < 2 ^ 16 by decide),
      movw_val (show dig h.sh < 2 ^ 16 by show h.D < 2 ^ 16; omega_arith), Impl.RsaOaep.Arm.sSrc,
      Impl.RsaOaep.Arm.sSrcLen, Impl.RsaOaep.Arm.sDst, Impl.RsaOaep.Arm.sDstLen]
    rfl
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR L Impl.RsaOaep.Arm.sDst, slotR L Impl.RsaOaep.Arm.sDstLen, slotR L Impl.RsaOaep.Arm.sSrc,
      slotR L Impl.RsaOaep.Arm.sSrcLen] s.mem t.mem := by
    rw [m]
    exact ((((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))).trans ((slot_frame _ _ _ _).mono (by simp))
  have dS : ∀ r ∈ [slotR L Impl.RsaOaep.Arm.sDst, slotR L Impl.RsaOaep.Arm.sDstLen, slotR L Impl.RsaOaep.Arm.sSrc,
      slotR L Impl.RsaOaep.Arm.sSrcLen], ∀ o n, o + n ≤ oRsa → (sR P.scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have hem : EMv P t.mem (emC h P σ) := fun i hi => by
    rw [← he i hi]
    exact fr _ fun r hr => dS r hr (oEm + i) 1 (by have := hi₀.k1024; pomega) _ (Region.contains_self _ _)
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨hk.1.keep h fr fun r hr => ?_,
    sbytes_keep fr (fun r hr => dS r hr _ _ (by pomega)) (by pomega) hk.2⟩, ?_, ?_, ?_, ?_⟩, hem⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact away3_slot (by decide) (by decide)
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]

/-- `maskedDB`, before its first byte's top bits are cleared, by MGF1 with
the hash function `g` of the table `mgf1`. -/
theorem mask_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) ∧ s.syms = σ.syms)
      (mgfPart fg h.sh 23)
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
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_arith
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_arith
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have e1 : oEm = 0 := rfl
  have e2 : Impl.RsaOaep.Arm.oBuf = 1024 := rfl
  have fit := hg.fit
  have fd : oEm + lo P + dbN h P ≤ Impl.RsaOaep.Arm.oBuf := by omega_arith
  -- What MGF1 writes misses the parameters and the bytes of `EM` outside `DB`.
  have away : ∀ r ∈ RsaOaep.Arm.mgfW g (P.lay h.D) P.scr (oEm + lo P) (dbN h P), Away3 (P.lay h.D) r :=
    fun r hr => ⟨RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
      RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
      RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr⟩
  have mp := RsaOaep.Arm.mpOf g hg (so := oEm + lo P + dbN h P) (sl := h.D) (dOff := oEm + lo P) (dl := dbN h P)
    h.D_pos (by omega_arith) (by omega_arith) fd (.inr (Nat.le_refl _)) (seed := Hs h P) (Hs_length h P)
    (X := Ko h P) (fun σ m m' ⟨hk, h0, hbc⟩ hf' => ⟨hk.keep h hf' away, fun i hi => by
      rw [← h0 i hi]
      exact hf' _ fun r hr => RsaOaep.Arm.mgfW_byte g hg fd (o := oEm + i) (by omega_arith) (by omega_arith) r hr _
        (Region.contains_self _ _), by
      rw [← hbc]
      exact hf' _ fun r hr => RsaOaep.Arm.mgfW_byte g hg fd (o := oEm + (P.K - 1)) (by omega_arith) (by omega_arith) r
        hr _ (Region.contains_self _ _)⟩)
    (j := 23) (by simp) hi₀.tbl (fun σ m hk => Q.t σ hk.1.1.tabT) Q.gne
  refine (VP.syms (slots_vp h P ⟨σ₀, hi₀⟩)).seq ((RsaOaep.Arm.mgf_vp g mp (arg_lt (by decide))
    (dstv := dbv h P)).mono (fun σ s ⟨⟨hc, ⟨hk, hs⟩, he⟩, sy⟩ => ⟨⟨hc, ⟨⟨hk.1, fun i hi => ?_, ?_⟩, hs⟩, fun i hi => ?_,
      fun i hi => ?_⟩, sy⟩) fun σ s ⟨⟨hc, ⟨hk, _⟩, hd, hh⟩, sy⟩ => ⟨⟨hc, hk, hd, hh⟩, sy⟩)
  · rw [he i (by omega_arith)]
    unfold emC emB emA
    rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), ite_eq_left hi]
  · rw [he _ (by omega_arith)]
    exact ite_eq_left rfl
  · rw [Nat.add_assoc, he _ (by omega_arith)]
    unfold emC emB emA
    rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left (by omega_arith),
      Nat.add_sub_cancel_left]
  · rw [Nat.add_assoc, Nat.add_assoc, he _ (by omega_arith)]
    unfold emC emB
    rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left (by omega_arith)]
    congr 1; omega_arith

/-- `EM`, as the specification encodes it (`RsaPss.emT`). -/
abbrev emF (G : Spec.Mgf1.Hash) (P : EP) (σ : State) (i : Nat) : Byte :=
  RsaPss.emT (lo P) (dbN h P) P.sl (saltB P σ) (Hs h P σ) (mkS h G P σ) ((cW (xB P)).setWidth 8) i

theorem andByte (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 := by
  have e1 : (b.setWidth 32).setWidth 8 = b := by simp
  rw [BitVec.setWidth_and, e1]

theorem topAnd_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0])
    (.block topAnd) hc).isSome = true := ⟨_, by taint_decide⟩

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
  have hlo : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have hdb : P.sl + 1 ≤ dbN h P := by unfold dbN; have := hf.2; omega_arith
  have hsum : lo P + dbN h P + h.D + 1 = P.K := by unfold dbN; have := hf.2; omega_arith
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h G P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ s.gpr .r1 = cW (xB P))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hk, hd, hh⟩ => ?_)
    (VP.taint _ topAnd_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hk, hd, hh⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block topSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = cW (xB P) := by
      prun [topSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1,
        hk.1.2.2.2.1, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hd, m ▸ hh⟩, r0, r1⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega_arith)
    have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega_arith)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega_arith)
    have hw : WP isa (.block topAnd) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + lo P)) (s.mem (sa P.scr (oEm + lo P)) &&& (cW (xB P)).setWidth 8) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [topAnd, r0, r1, ad, rd, wd, dpVal, andByte]
    refine WP.mono hw fun t ⟨m, rd', wr', sp'⟩ => ?_
    have fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_arith) (by omega_arith)
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd' wr' sp', hk.1.keep h fr fun r hr => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith) (by rw [hg.F]; decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by omega_arith)
    rw [m, sa_write P.scr _ _ (by omega_arith) (by omega_arith)]
    have hl := Hs_length h P σ
    unfold emF RsaPss.emT
    by_cases h1 : i < lo P
    · rw [ite_eq_right (by omega_arith), ite_eq_left h1]; exact hk.2.1 i h1
    rw [ite_eq_right h1]
    by_cases h2 : i - lo P < dbN h P
    · rw [ite_eq_left h2]
      by_cases h3 : i - lo P = 0
      · rw [ite_eq_left (by omega_arith), ite_eq_left h3, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega_arith), h3]
      · rw [ite_eq_right (by omega_arith), ite_eq_right h3, show oEm + i = oEm + lo P + (i - lo P) by omega_arith, hd _ h2]
    rw [ite_eq_right h2, ite_eq_right (by omega_arith)]
    by_cases h4 : i - lo P < dbN h P + (Hs h P σ).length
    · rw [ite_eq_left h4, show oEm + i = oEm + lo P + dbN h P + (i - lo P - dbN h P) by omega_arith, hh _ (by omega_arith)]
    · rw [ite_eq_right h4, show oEm + i = oEm + (P.K - 1) by omega_arith]; exact hk.2.2

/-- The encoding, when everything fits. -/
theorem enc_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => E0 h P σ s ∧ s.syms = σ.syms) (signEnc f fg h.sh)
      (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h g.G P σ)) ∧ s.syms = σ.syms) := by
  show VP _ (.seq (yDig h.sh 16) (.seq (.block (cpSalt h.sh)) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (lenSet h.sh 19)) (.seq (ctHash f h.sh 22) (.seq (.block clrEm) (.seq Impl.Bignum.Arm.maskBytes
    (.seq (.block saltPos) (.seq (.block put1) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (putH h.sh)) (.seq Impl.Bignum.Arm.copyBytes (.seq (.block bcSet) (.seq (.block bcPut)
    (.seq (mgfPart fg h.sh 23) (.seq (.block topSet) (.block topAnd))))))))))))))))) _
  exact (VP.syms (yDig_sg h P hP)).seq (VP.assoc ((VP.syms (salt_vp h P hP)).seq ((VP.syms (lenSet_vp h P)).seq
    ((hash_vp h P Q hP).seq (VP.assoc ((VP.syms (clr_vp h P hP)).seq (VP.assoc ((VP.syms (one_vp h P hP)).seq
    ((VP.syms (cpS_vp h P hP)).seq (VP.assoc ((VP.syms (putH_vp h P hP)).seq (VP.assoc ((VP.syms (bc_vp h P hP)).seq
    ((mask_vp h P Q hP).seq (VP.syms (top_vp h g.G P hP))))))))))))))))

end VG.Proof.RsaPss.Arm.Sg
