import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrw wp_lsr)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (parseBoth epi rawWith)

def publicRegs : VG.AArch64.Taint.T := Taint.ofRegs [.x0,.x2,.x3,.x4]
def publicInputs (s t : State) : Prop := VG.AArch64.Taint.Agree publicRegs s t ∧
  (s.gpr .x1).setWidth 32=(t.gpr .x1).setWidth 32
def gammaCode : Prog isa := .block [.ldr .w .x27 .x19 7904,.lsr .x .x9 .x27 18]
def afterGamma : Prog isa := .seq (.ite (.zero .x .x9) (parseBoth 18) (parseBoth 20)) (.block epi)
def gammaValue (σ : State) : BitVec 64 := (σ.gpr .x1).setWidth 32 |>.setWidth 64 |>.ushiftRight 18

theorem gamma_ok {σ s : State} (hp : Pre σ) (he : Env σ s) :
    WP isa gammaCode s fun t => Env σ t ∧ t.gpr .x9=gammaValue σ := by
  refine wp_ldrw (a := σ.gpr .x4+7904) ⟨by decide,by decide⟩ (by rw [he.base]; rfl)
    (by rw [he.rd,he.wr]
        exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ (by decide) (by decide)⟩)
    fun a ha ea => wp_lsr (by decide) fun t ht et => WP.block_nil_iff.mpr ?_
  have hk := (ha.trans ht).mono (rs' := [.x27,.x9]) (by simp)
  refine ⟨he.lowStep (RegKeep.only hk) (W := [])
    (by rw [ht.mem,ha.mem]; exact Frame.refl _ _) (by decide) (by simp),?_⟩
  rw [et,ea,he.gamma]; rfl

private theorem afterGamma_ct :
    RelCT isa (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x21,.x22,.x9])) afterGamma (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x19,.x21,.x22,.x9]) (fun _ _ h => h) (by taint_decide)

/-- A public gamma value may make a memory round trip; the seeds and all
SHAKE lanes remain secret. The correctness invariant recovers only gamma. -/
theorem rawWith_ct (core : Resident.Core)
    (hc : RelCT isa (VG.AArch64.Taint.Agree publicRegs) (beforeDispatch core.code) (fun _ _ => True)) :
    ConstantTime isa Pre publicInputs (rawWith core.code) := by
  intro σ τ tr1 tr2 u v hp hq hpub e1 e2
  have front : RelCT isa (fun s t => s=σ ∧ t=τ) (beforeDispatch core.code)
      (fun s t => Env σ s ∧ Env τ t) := by
    apply RelCT.mono (RelCT.wp (F₁ := SpongePost σ) (F₂ := SpongePost τ) (RelCT.mono hc (fun s t h => by rcases h with ⟨rfl,rfl⟩; exact hpub.1)
      (fun _ _ _ => True.intro)) ?_) (fun _ _ h => h) (fun _ _ h => ⟨h.2.1.1,h.2.2.1⟩)
    intro s t h
    rw [h.1,h.2]
    exact ⟨beforeDispatch_ok core σ hp,beforeDispatch_ok core τ hq⟩
  have gamma : RelCT isa (fun s t => Env σ s ∧ Env τ t) gammaCode
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x21,.x22,.x9])) := by
    have check : RelCT isa (fun s t => Env σ s ∧ Env τ t) gammaCode (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x19]) (fun s t h => by
        refine ⟨h.1.sp.trans (hpub.1.1.trans h.2.sp.symm),?_⟩
        intro r hr; simp only [Taint.mem_ofRegs,List.mem_singleton] at hr; subst r
        exact h.1.base.trans ((hpub.1.2 .x4 (by simp [publicRegs])).trans h.2.base.symm)) (by taint_decide)
    apply RelCT.mono (RelCT.wp check (fun _ _ h => ⟨gamma_ok hp h.1,gamma_ok hq h.2⟩))
      (fun _ _ h => h) ?_
    intro s t ⟨_,⟨hs,h9s⟩,⟨ht,h9t⟩⟩
    refine ⟨hs.sp.trans (hpub.1.1.trans ht.sp.symm),?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hs.base.trans ((hpub.1.2 .x4 (by simp [publicRegs])).trans ht.base.symm)
    · exact hs.out1.trans ((hpub.1.2 .x2 (by simp [publicRegs])).trans ht.out1.symm)
    · exact hs.out2.trans ((hpub.1.2 .x3 (by simp [publicRegs])).trans ht.out2.symm)
    · rw [h9s,h9t,gammaValue,gammaValue,hpub.2]
  have all := RelCT.assoc (RelCT.seq front (RelCT.seq gamma afterGamma_ct))
  exact (all _ _ _ _ _ _ ⟨rfl,rfl⟩ e1 e2).1

private theorem original_front_ct :
    RelCT isa (VG.AArch64.Taint.Agree publicRegs)
      (beforeDispatch Resident.originalCore.code) (fun _ _ => True) :=
  RelCT.taint (A := taint) publicRegs (fun _ _ h => h) (by taint_decide)

private theorem n2_front_ct :
    RelCT isa (VG.AArch64.Taint.Agree publicRegs)
      (beforeDispatch Resident.n2Core.code) (fun _ _ => True) :=
  RelCT.taint (A := taint) publicRegs (fun _ _ h => h) (by taint_decide)

theorem raw_ct : ConstantTime isa Pre publicInputs
    Impl.MlDsa.AArch64.Optimized.ResidentMask.raw :=
  rawWith_ct Resident.originalCore original_front_ct

theorem raw_n2_ct : ConstantTime isa Pre publicInputs
    (rawWith Resident.n2Core.code) := rawWith_ct Resident.n2Core n2_front_ct

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
