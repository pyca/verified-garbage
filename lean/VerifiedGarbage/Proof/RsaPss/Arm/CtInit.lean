module

public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
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

`init_vp`: the streaming `init` sets the hash value at `oSt` to the initial
one. `lenBlk_vp`: the block at `oLen` holds zeros then the length field of
`ℓ` (slot `sL`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The 16 bytes below the stack pointer, where a streaming function's frame
goes, are in our callees' stack. -/
theorem below_low (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) :
    Region.Sub (Pbkdf2.Stream.Arm.below s) L.LOW := by
  have hC := hg.C16
  have hB := hc.st.ok.B56
  rw [Pbkdf2.Stream.Arm.below, hc.st.sp]
  show Region.Sub ⟨State.addr L.B - BitVec.ofNat 64 16, 16⟩ ⟨State.addr L.B - BitVec.ofNat 64 L.C, L.C⟩
  exact Offset.sub_below _ hC (by omega)

/-- The streaming `init` on the hash value at `oSt`. -/
theorem init_vp (hg : Geo L scr) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt (h.N + h.B), L.LOW] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem)
      (.seq (.block initArgs) (.call h.H.md.st.initN h.H.md.st.initC))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSt) = h.ok.iv) := by
  have hN := h.N_le
  have hBl := h.B_le
  have fit := hg.fit
  have hS := h.S_eq
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt)
    (VP.blk (by decide) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi⟩ => ?_) ?_
  · prun [initArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi,
      movw_val (show oSt < 2 ^ 16 by decide)]
  have fitS : (scr + BitVec.ofNat 32 oSt).toNat + h.H.md.st.S ≤ 2 ^ 32 := by
    rw [hg.scr_lt (by decide), hS]; unfold oSt oRsa at *; omega
  have cov : ∀ σ s, Ctx L scr σ s → Covers [⟨State.addr (scr + BitVec.ofNat 32 oSt), h.H.md.st.S⟩] s.wr :=
    fun σ s hc => by
      rw [hg.addr (by decide)]; refine Covers.one ?_
      rw [hS]; exact hg.wr hc.st (by unfold oSt oRsa; omega)
  refine VP.of_ct (fun _ _ => Pbkdf2.Stream.Arm.init_rel h.ok.stream (st := scr + BitVec.ofNat 32 oSt)
    fun a b hab => ⟨hab.1.2.2, hab.2.2.2, fitS, cov _ _ hab.1.1, cov _ _ hab.2.1⟩) ?_
  rintro σ s ⟨hc, hi, r0⟩
  refine Pbkdf2.Stream.Arm.init_call h.ok.stream r0 fitS (cov _ _ hc) fun s' af rp => ?_
  have fr : Frame [sR scr oSt (h.N + h.B), L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [hg.addr (by decide), hS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) af.rd af.wr af.sp, hI σ _ _ hi fr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.inW (by unfold oSt oRsa; omega)
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨σ', ok⟩ := hg.ok
      exact hg.slot ok (by unfold oSt oRsa; omega) (by rw [hg.F]; decide)
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega)
  · obtain ⟨e, -⟩ := h.ok.repr _ _ _ (by rw [hg.addr (by decide)] at rp; exact rp)
    rw [e, List.length_nil, Nat.zero_div, MdStream.Md.compressList_zero]

end VG.Proof.RsaPss.Arm
