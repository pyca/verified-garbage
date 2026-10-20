module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc2
public import VerifiedGarbage.Proof.RsaPss.EncBytes
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

/-- The mask. -/
abbrev mkS (P : EP) (σ : State) : List Byte := Spec.Mgf1.mgf1 h.G (Hs h P σ) (dbN h P)

theorem Hs_length (P : EP) (σ : State) : (Hs h P σ).length = h.D := by
  rw [Hs, ← h.hash]; have := (PssHash.valid h).2 (Mp h P σ); rw [this, h.glen]

/-- `maskedDB`, before its first byte's top bits are cleared. -/
theorem mask_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ke h P σ s.mem ∧ EMv P s.mem (emC h P σ)) (mgfXor h.H)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h P σ).getD i 0) ∧
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
  have hB := h.B_le
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 2048 := rfl
  have fit := hg.fit
  -- What `mgfXor` writes misses the parameters and the bytes of `EM` outside `DB` and `H`.
  have away : ∀ r ∈ mgfW h (P.lay h.D) P.scr (lo P) (dbN h P), Away3 (P.lay h.D) r ∧
      ∀ i, (i < lo P ∨ i = P.K - 1) → ¬ r.Contains (sa P.scr (oEm + i)) 1 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · refine ⟨away3_ctW h hg (by omega) r hr, fun i hi => ?_⟩
      exact ctW_em h hg (T := h.B) (o := oEm + i) (n := 1) (by omega) (by omega) (by omega) r hr _
        (Region.contains_self _ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨away3_scr hg (by omega), fun i hi => Geo.sep (scr := P.scr) (o := oEm + i) (n := 1) (by omega)
          (by omega) (by omega) _ (Region.contains_self _ _)⟩
      all_goals exact ⟨away3_slot (by decide) (by decide), fun i hi => (hg.slot ok (o := oEm + i) (n := 1) (by omega)
        (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)⟩
  have mp : MP h (P.lay h.D) P.scr (lo P) (dbN h P) (Hs h P) (Ko h P) := by
    refine ⟨hg, by omega, by omega, Hs_length h P, fun σ m m' ⟨hk, h0, hbc⟩ hf' => ⟨hk.keep h hf' fun r hr =>
      (away r hr).1, fun i hi => ?_, ?_⟩, fun σ m hk => hk.1.2.2.2.1, fun σ m hk => hk.1.2.2.2.2⟩
    · rw [← h0 i hi]; exact hf' _ fun r hr => (away r hr).2 i (.inl hi)
    · rw [← hbc]; exact hf' _ fun r hr => (away r hr).2 _ (.inr rfl)
  refine (mgf_vp h mp (dbv := dbv h P)).mono (fun σ s ⟨hc, hk, he⟩ => ⟨hc, ⟨hk.1, fun i hi => ?_, ?_⟩, fun i hi => ?_,
    fun i hi => ?_⟩) fun σ s h => h
  · rw [he i (by omega)]
    unfold emC emB emA
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left hi]
  · rw [he _ (by omega)]
    exact ite_eq_left rfl
  · rw [Nat.add_assoc, he _ (by omega)]
    unfold emC emB emA
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  · rw [Nat.add_assoc, Nat.add_assoc, he _ (by omega)]
    unfold emC emB
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega

/-- `EM`, as the specification encodes it (`RsaPss.emT`). -/
abbrev emF (P : EP) (σ : State) (i : Nat) : Byte :=
  RsaPss.emT (lo P) (dbN h P) P.sl (saltB P σ) (Hs h P σ) (mkS h P σ) ((cW (xB P)).setWidth 8) i

theorem andByte (b : Byte) (w : BitVec 32) : (b.setWidth 32 &&& w).setWidth 8 = b &&& w.setWidth 8 := by
  have e1 : (b.setWidth 32).setWidth 8 = b := by simp
  rw [BitVec.setWidth_and, e1]

theorem topAnd_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0])
    (.block topAnd) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `maskedDB`'s first byte ANDed with the mask: `EM`. -/
theorem top_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Ko h P σ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h P σ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (Hs h P σ).getD i 0)
      (.seq (.block topSet) (.block topAnd))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ)) := by
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
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbv h P σ i ^^^ (mkS h P σ).getD i 0) ∧
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
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega)
    have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega)
    have wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega)
    have hw : WP isa (.block topAnd) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + lo P)) (s.mem (sa P.scr (oEm + lo P)) &&& (cW (xB P)).setWidth 8) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [topAnd, r0, r1, ad, rd, wd, dpVal, andByte]
    refine WP.mono hw fun t ⟨m, rd', wr', sp'⟩ => ?_
    have fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega) (by omega)
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd' wr' sp', hk.1.keep h fr fun r hr => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega) (by rw [hg.F]; decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by omega)
    rw [m, sa_write P.scr _ _ (by omega) (by omega)]
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

/-- The encoding, when everything fits. -/
theorem enc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (E0 h P) (signEnc h.H)
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem ∧ EMv P s.mem (emF h P σ)) := by
  show VP _ (.seq (yDig h.H 16) (.seq (.block (cpSalt h.H)) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (lenSet h.H 18)) (.seq (ctHash h.H) (.seq (.block clrEm) (.seq Impl.Bignum.Arm.maskBytes
    (.seq (.block saltPos) (.seq (.block put1) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (putH h.H)) (.seq Impl.Bignum.Arm.copyBytes (.seq (.block bcSet) (.seq (.block bcPut)
    (.seq (mgfXor h.H) (.seq (.block topSet) (.block topAnd))))))))))))))))) _
  exact (yDig_sg h P hP).seq (VP.assoc ((salt_vp h P hP).seq ((lenSet_vp h P).seq ((hash_vp h P hP).seq
    (VP.assoc ((clr_vp h P hP).seq (VP.assoc ((one_vp h P hP).seq ((cpS_vp h P hP).seq
    (VP.assoc ((putH_vp h P hP).seq (VP.assoc ((bc_vp h P hP).seq ((mask_vp h P hP).seq (top_vp h P hP)))))))))))))))

end VG.Proof.RsaPss.Arm.Sg
