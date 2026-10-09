import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRoundTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAdaptive

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure FlaggedPair (σ τ s t : State) (A B : Nat→Spec.Sha3.State) (L M : Nat→List Zq) : Prop where
 left : SamplerRun σ s A L
 right : SamplerRun τ t B M
 leftFlag : s.gpr .x27=countFlag L
 rightFlag : t.gpr .x27=countFlag M

theorem countFlag_length {L M : Nat→List Zq} (h : ∀i<4,(L i).length=(M i).length) :
    countFlag L=countFlag M := by
  unfold countFlag foldedFlags
  change ((BitVec.ofNat 64 (256-(L 0).length)|||BitVec.ofNat 64 (256-(L 1).length))|||
    BitVec.ofNat 64 (256-(L 2).length))|||BitVec.ofNat 64 (256-(L 3).length)=_
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)]
  rfl

theorem flagsStage_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerBases σ τ)
    {A B : Nat→Spec.Sha3.State} {L M : Nat→List Zq} :
    RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags)
      (fun s t=>FlaggedPair σ τ s t A B L M) := by
  obtain ⟨_,hc⟩:=flags_taint
  have ct : RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.flags) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp) (fun r hr=>by
        rw [List.mem_singleton.mp hr,h.1.env.x19,h.2.env.x19]; exact hb.scratch)) hc
  exact (ct.wp (fun _ _ h=>⟨flagsStage_ok hp h.1,flagsStage_ok hq h.2⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>⟨h.2.1.1,h.2.2.1,h.2.1.2,h.2.2.2⟩)

theorem secondBatch_relCT (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerBases σ τ)
    {A B : Nat→Spec.Sha3.State} {L M : Nat→List Zq}
    (hl : ∀i<4,(L i).length=(M i).length)
    (hx : ∀i<4,(chunkBytes (A i)).map (hbOks η)=(chunkBytes (B i)).map (hbOks η)) :
    RelCT isa (fun s t=>FlaggedPair σ τ s t A B L M) (secondBatch sha3 η)
      (fun s t=>(∃A',SamplerRun σ s A' (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        s.gpr .x27=countFlag (fun i=>rbFold η (L i) (chunkBytes (A i)))) ∧
        (∃B',SamplerRun τ t B' (fun i=>rbFold η (M i) (chunkBytes (B i))) ∧
        t.gpr .x27=countFlag (fun i=>rbFold η (M i) (chunkBytes (B i))))) := by
  have ct : RelCT isa (fun s t=>FlaggedPair σ τ s t A B L M) (secondBatch sha3 η)
      (fun _ _=>True) := by
    unfold secondBatch
    refine RelCT.ite (fun s t h=>by
      rw [VG.Proof.MlKem.AArch64.eval_zero,VG.Proof.MlKem.AArch64.eval_zero,
        h.leftFlag,h.rightFlag,countFlag_length hl]) ?_ ?_
    · have hn : ∃hint,(taint.check (Taint.ofRegs []) (.block ([] : List Instr)) hint).isSome=true:=⟨_,by taint_decide⟩
      obtain ⟨_,hn⟩:=hn
      exact RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
        (by rw [h.1.left.env.sp,h.1.right.env.sp]; exact hb.sp)
        (fun _ hr=>False.elim (List.not_mem_nil hr))) hn
    · exact (RelCT.assoc (RelCT.seq (sampleRound_relCT sha3 hη (Or.inr rfl) hp hq hb hl hx)
        (flagsStage_relCT hp hq hb))).mono
          (fun _ _ h=>⟨h.1.left,h.1.right⟩) (fun _ _ _=>True.intro)
  exact (ct.wp (fun _ _ h=>⟨secondBatch_ok sha3 hη hp h.left h.leftFlag,
      secondBatch_ok sha3 hη hq h.right h.rightFlag⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
