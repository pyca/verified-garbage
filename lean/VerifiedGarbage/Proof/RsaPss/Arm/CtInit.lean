module

public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
import VerifiedGarbage.Proof.Framework.Arm.Syms
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSASSA-PSS on ARMv7: hashing, the hash value and the length field

`init_vp`: the table of `MdHash` that is our argument `j` to the slot
`sTab`, and its streaming `init`, called through the table, sets the hash
value at `oSt` to the initial one.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (tA tabA_wp)
open VG.Impl.RsaOaep.Arm (sTab)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The slot `sTab`, apart from our part of `scratch` and from the slots
`ctHash` writes. -/
theorem sTab_sep (hg : Geo L scr) {o n : Nat} (h : o + n ≤ oRsa) : (slotR L sTab).Disjoint (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact hg.slot ok h (by rw [hg.F]; decide)

/-- The table that is our argument `j` to `sTab`, and the streaming `init`,
through the table, on the hash value at `oSt`. -/
theorem init_vp (hg : Geo L scr) {f : MdFns} {dn : String} {j : Nat} {ai ac ad : BitVec 32}
    (hj : j < L.argv.length) (hoff : arg j < 4096)
    (hR : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA (L.argv.getD j 0) o) 4) (hne : f.init ≠ [])
    {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt (h.N + h.B), L.LOW, slotR L sTab] m m' → Inv σ m')
    (htab : ∀ σ m, Inv σ m → HTab h dn f (L.argv.getD j 0) ai ac ad σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem) ∧ s.syms = σ.syms)
      (initPart f j)
      (fun σ s => (Ctx L scr σ s ∧ (Inv σ s.mem ∧ s.mem.readW (L.fr sTab) 32 = L.argv.getD j 0) ∧
        h.md.stateAt s.mem (sa scr oSt) = h.ok.iv) ∧ s.syms = σ.syms) := by
  have hN := h.N_le
  have hBl := h.B_le
  have fit := hg.fit
  have hS := h.S_eq
  obtain ⟨σ', ok⟩ := hg.ok
  let p := L.argv.getD j 0
  let F₀ : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ (Inv σ s.mem ∧ s.mem.readW (L.fr sTab) 32 = p)) ∧
    s.syms = σ.syms
  let F₁ : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ (Inv σ s.mem ∧ s.mem.readW (L.fr sTab) 32 = p) ∧
    s.gpr .r0 = scr + BitVec.ofNat 32 oSt) ∧ s.syms = σ.syms
  have dT : (slotR L sTab).Disjoint (slotR L sS) := Lay.fr_sep (by decide) (by decide) (by decide)
  refine VP.seq (G := F₀)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s ⟨⟨hc, hi⟩, sy⟩ => ?_)
    (VP.seq (G := F₁)
      (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s ⟨⟨hc, hi, ht⟩, sy⟩ => ?_)
      ?_)
  · refine WP.mono (tabA_wp hg hc hj hoff) fun t ⟨m, rd, wr, sp, _, _, ty⟩ => ?_
    have fr : Frame [slotR L sTab] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    have hc' : Ctx L scr σ t := hc.write fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; decide)⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT.symm) rd wr sp
    exact ⟨⟨hc', hI σ _ _ hi (fr.mono fun r hr => by simp at hr; simp [hr]), by rw [m, Mem.readW_writeW_self32]⟩,
      ty.trans sy⟩
  · prun [initArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi, ht,
      movw_val (show oSt < 2 ^ 16 by decide), VG.Arm.RegUpd.syms_setReg, sy, F₁]
  have fitS : (scr + BitVec.ofNat 32 oSt).toNat + h.H.md.st.S ≤ 2 ^ 32 := by
    rw [hg.scr_lt (by decide), hS]; unfold oSt oRsa at *; omega
  have cov : ∀ σ s, Ctx L scr σ s → Covers [⟨State.addr (scr + BitVec.ofNat 32 oSt), h.H.md.st.S⟩] s.wr :=
    fun σ s hc => by
      rw [hg.addr (by decide)]; refine Covers.one ?_
      rw [hS]; exact hg.wr hc.st (by unfold oSt oRsa; omega)
  refine htcall_vp hg (F := F₁) (fun σ s hs => ⟨hs.1.1, hs.2, hs.1.2.1.2⟩)
    (fun σ s v ⟨⟨hc, hi, r0⟩, sy⟩ => ⟨⟨Ctx.setReg_iff.mpr hc, hi, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r0⟩, sy⟩) hR (k := 0) (by decide) hne
    (fun σ s hs => let T := htab σ _ hs.1.2.1.1; ⟨T.m0, T.i⟩) ?_
  refine VP.of_ct (fun _ _ => Pbkdf2.Stream.Arm.init_rel h.ok.stream (st := scr + BitVec.ofNat 32 oSt)
    fun a b hab => ⟨hab.1.1.2.2, hab.2.1.2.2, fitS, cov _ _ hab.1.1.1, cov _ _ hab.2.1.1⟩) ?_
  rintro σ s ⟨⟨hc, ⟨hi, ht⟩, r0⟩, sy⟩
  refine WP.mono_syms (Pbkdf2.Stream.Arm.init_call h.ok.stream r0 fitS (cov _ _ hc) fun s' af rp => ?_)
    fun s' hq sy' => ⟨hq, sy'.trans sy⟩
  have fr : Frame [sR scr oSt (h.N + h.B), L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [hg.addr (by decide), hS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) af.rd af.wr af.sp,
    ⟨hI σ _ _ hi (fr.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp), slot_keep fr (fun r hr => ?_) ht⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.inW (by unfold oSt oRsa; omega)
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.slot ok (by unfold oSt oRsa; omega) (by rw [hg.F]; decide)
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sTab_sep hg (by unfold oSt oRsa; omega)
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega)
  · obtain ⟨e, -⟩ := h.ok.repr _ _ _ (by rw [hg.addr (by decide)] at rp; exact rp)
    rw [e, List.length_nil, Nat.zero_div, MdStream.Md.compressList_zero]

end VG.Proof.RsaPss.Arm
