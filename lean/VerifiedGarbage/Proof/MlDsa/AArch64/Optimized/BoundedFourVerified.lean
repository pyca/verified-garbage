import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourShake
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Spec.MlDsa.BoundedFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourOuterTaint
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRound
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourAdaptive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFinish
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified

/-! ## From `BoundedFourSmall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- Failure masking is per lane, so every output remains a small polynomial
regardless of the aggregate four-lane return value. -/
theorem Result.small {σ t : State} {η : Nat} (h : Result σ t (sampledRows σ η))
    {i : Nat} (hi : i<4) :
    ∃x : IPoly,polyAt t.mem (outputAt (samplerOut σ) i)=toRq x ∧
      VG.Proof.MlDsa.KeyGen.Small η x := by
  by_cases hf : (sampledRows σ η i).length=256
  · have hs := rejBounded_some η
      (ρ := Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66) (B := 544)
      (by simpa only [sampledRows_H] using hf)
    obtain ⟨x,hx,he⟩:=Option.map_eq_some_iff.mp hs
    refine ⟨x,?_,VG.Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    rw [h.full hi hf,sampledRows_H]
    exact he.symm
  · refine ⟨Vector.replicate 256 0,?_,VG.Proof.MlDsa.KeyGen.small_zero η⟩
    apply Vector.ext
    intro j hj
    simp only [polyAt,Vector.getElem_ofFn,h.words i hi j hj,resultWord,ite_eq_right hf,
      toRq,Vector.getElem_map,Vector.getElem_replicate]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourChunkLeak.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- The public transcript already determines each stream's rejection bits. -/
theorem fourLeak_stream {η : Nat} {σ τ : State}
    (h : rejBoundedFourLeak η σ.mem (samplerSeed σ)=
      rejBoundedFourLeak η τ.mem (samplerSeed τ)) {i : Nat} (hi : i<4) :
    rejBoundedLeak η (Spec.Sha3.bytesAt σ.mem (samplerSeedAt σ i) 66)=
      rejBoundedLeak η (Spec.Sha3.bytesAt τ.mem (samplerSeedAt τ i) 66) := by
  exact VG.Proof.MlDsa.KeyGen.flatMap_range_inj
    (fun _=>VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _)
    (fun _=>VG.Proof.MlDsa.KeyGen.rejBoundedLeak_length _ _) h i hi

/-- Splitting the original SHAKE rejection transcript adds no observable data. -/
theorem fourLeak_chunks {η : Nat} {σ τ : State}
    (h : rejBoundedFourLeak η σ.mem (samplerSeed σ)=
      rejBoundedFourLeak η τ.mem (samplerSeed τ)) {i : Nat} (hi : i<4) :
    (chunkBytes (samplerA σ i)).map (hbOks η)=
      (chunkBytes (samplerA τ i)).map (hbOks η) ∧
    (chunkBytes (Resident.permuted (samplerA σ i) 2)).map (hbOks η)=
      (chunkBytes (Resident.permuted (samplerA τ i) 2)).map (hbOks η) := by
  have he := leak_hbOks (fourLeak_stream h hi) (B := 544) (by decide)
  rw [←chunks_H,←chunks_H,List.map_append,List.map_append] at he
  exact List.append_inj he (by simp only [List.length_map,chunkBytes_length])

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourBatchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

theorem BatchInv.parseReady {σ s : State} {b p : Addr} {i off : Nat}
    {L : Nat→List Zq} {X : Nat→List Byte} (hi : i<4)
    (hy : BatchLayout σ b p off X) (hs : BatchInv σ s b p L) :
    ParseReady i off (b+6000) (outputAt p i) (inputAt b i off) (countAt b i) (L i) (X i) s :=
  ⟨hs.fields.bound i hi,hy.length i hi,
    (hy.vector i hi).frame hs.keep hs.frame (hy.streamsApart i hi),
    (hy.scalar i hi).frame hs.keep hs.frame (hy.streamsApart i hi),hs.table,hs.fields.stored i hi,
    by rw [hs.base]; rfl,by rw [hs.output]; rfl,by rw [hs.base]; rfl,
    by rw [hs.base],hs.fields.count i hi,
    by rw [hs.keep.rd,hs.keep.wr]; exact hy.countRead i hi⟩

theorem updateBatch_length {η i : Nat} {L M : Nat→List Zq} {X Y : Nat→List Byte}
    (hi : i<4) (hl : ∀j<4,(L j).length=(M j).length)
    (hx : ∀j<4,(X j).map (hbOks η)=(Y j).map (hbOks η)) :
    ∀j<4,(updateBatch η i L X j).length=(updateBatch η i M Y j).length := by
  intro j hj
  unfold updateBatch
  by_cases he : j=i
  · rw [ite_eq_left he,ite_eq_left he]
    exact rbFold_length_congr (hl i hi) (hx i hi)
  · rw [ite_eq_right he,ite_eq_right he]
    exact hl j hj

theorem batchStep_relCT {σ τ : State} {b p : Addr} {η i off : Nat}
    (hη : η=2∨η=4) (hi : i<4) (ho : off=0∨off=272)
    {L M : Nat→List Zq} {X Y : Nat→List Byte}
    (sx : BatchLayout σ b p off X) (sy : BatchLayout τ b p off Y) (hsp : σ.sp=τ.sp)
    (hl : ∀j<4,(L j).length=(M j).length)
    (hx : ∀j<4,(X j).map (hbOks η)=(Y j).map (hbOks η)) :
    RelCT isa (fun s t=>BatchInv σ s b p L ∧ BatchInv τ t b p M)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η i off)
      (fun s t=>BatchInv σ s b p (updateBatch η i L X) ∧ BatchInv τ t b p (updateBatch η i M Y)) := by
  have hc := (parse_relCT hη hi ho (hl i hi) (hx i hi)).mono
    (fun s t (h : BatchInv σ s b p L ∧ BatchInv τ t b p M)=>
      ⟨h.1.parseReady hi sx,h.2.parseReady hi sy,
        by rw [h.1.keep.sp,h.2.keep.sp]; exact hsp,
        by rw [h.1.base,h.2.base],by rw [h.1.output,h.2.output]⟩)
    (fun _ _ _=>True.intro)
  exact (hc.wp (fun _ _ h=>⟨batchStep_ok hη hi (by omega) sx h.1,
      batchStep_ok hη hi (by omega) sy h.2⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

theorem batch_relCT {σ τ : State} {b p : Addr} {η off : Nat}
    (hη : η=2∨η=4) (ho : off=0∨off=272)
    {L M : Nat→List Zq} {X Y : Nat→List Byte}
    (sx : BatchLayout σ b p off X) (sy : BatchLayout τ b p off Y) (hsp : σ.sp=τ.sp)
    (hl : ∀j<4,(L j).length=(M j).length)
    (hx : ∀j<4,(X j).map (hbOks η)=(Y j).map (hbOks η)) :
    RelCT isa (fun s t=>BatchInv σ s b p L ∧ BatchInv τ t b p M)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.batch true η off)
      (fun s t=>BatchInv σ s b p (fun i=>rbFold η (L i) (X i)) ∧
        BatchInv τ t b p (fun i=>rbFold η (M i) (Y i))) := by
  have h0:=updateBatch_length (η := η) (i := 0) (by decide) hl hx
  have h1:=updateBatch_length (η := η) (i := 1) (by decide) h0 hx
  have h2:=updateBatch_length (η := η) (i := 2) (by decide) h1 hx
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.batch
  refine RelCT.seq (batchStep_relCT hη (by decide : 0<4) ho sx sy hsp hl hx) ?_
  refine RelCT.seq (batchStep_relCT hη (by decide : 1<4) ho sx sy hsp h0 hx) ?_
  refine RelCT.seq (batchStep_relCT hη (by decide : 2<4) ho sx sy hsp h1 hx) ?_
  exact (batchStep_relCT hη (by decide : 3<4) ho sx sy hsp h2 hx).mono
    (fun _ _ h=>h) (fun _ _ h=>
      ⟨h.1.congr (fun _ hi=>updateBatch_four η L X hi),
       h.2.congr (fun _ hi=>updateBatch_four η M Y hi)⟩)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourRoundTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (squeezeTwo batch)

structure SamplerBases (σ τ : State) : Prop where
 scratch : samplerScratch σ=samplerScratch τ
 output : samplerOut σ=samplerOut τ
 sp : σ.sp=τ.sp

theorem sampleRound_relCT (sha3 : Bool) {η off : Nat} (hη : η=2∨η=4) (ho : off=0∨off=272)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerBases σ τ)
    {A B : Nat→Spec.Sha3.State} {L M : Nat→List Zq}
    (hl : ∀i<4,(L i).length=(M i).length)
    (hx : ∀i<4,(chunkBytes (A i)).map (hbOks η)=(chunkBytes (B i)).map (hbOks η)) :
    RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.seq (squeezeTwo sha3 off) (batch true η off))
      (fun s t=>SamplerRun σ s (fun i=>Resident.permuted (A i) 2)
        (fun i=>rbFold η (L i) (chunkBytes (A i))) ∧
        SamplerRun τ t (fun i=>Resident.permuted (B i) 2)
        (fun i=>rbFold η (M i) (chunkBytes (B i)))) := by
  obtain ⟨_,hc⟩:=squeezeTwo_taint sha3 ho
  have cs : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19)
      (squeezeTwo sha3 off) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      rw [List.mem_singleton.mp hr]; exact h.2)) hc
  have ct : RelCT isa (fun s t=>SamplerRun σ s A L ∧ SamplerRun τ t B M)
      (.seq (squeezeTwo sha3 off) (batch true η off)) (fun _ _=>True) := by
    intro s t tr ur u v h es et
    cases es with | seq es0 es1 =>
      cases et with | seq et0 et1 =>
        have e0:=(cs _ _ _ _ _ _ ⟨by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp,
          by rw [h.1.env.x19,h.2.env.x19]; exact hb.scratch⟩ es0 et0).1
        obtain ⟨_,_,ex,ha⟩:=squeezeStage_ok sha3 hp h.1 (by omega : off≤272)
        obtain ⟨_,_,ey,hd⟩:=squeezeStage_ok sha3 hq h.2 (by omega : off≤272)
        obtain ⟨_,rfl⟩:=Exec.det es0 ex
        obtain ⟨_,rfl⟩:=Exec.det et0 ey
        have lx : BatchLayout _ (samplerScratch σ) (samplerOut σ) off (fun i=>chunkBytes (A i)) :=
          samplerBatchLayout_ok hp ha.1.env.wr (by omega) (fun _ _=>chunkBytes_length _)
            (fun i hi j hj=>by rw [chunkBytes_get _ hj]; exact stream136_byte (ha.2 i hi) (by omega))
        have ly : BatchLayout _ (samplerScratch τ) (samplerOut τ) off (fun i=>chunkBytes (B i)) :=
          samplerBatchLayout_ok hq hd.1.env.wr (by omega) (fun _ _=>chunkBytes_length _)
            (fun i hi j hj=>by rw [chunkBytes_get _ hj]; exact stream136_byte (hd.2 i hi) (by omega))
        have ia : BatchInv _ _ (samplerScratch σ) (samplerOut σ) L :=
          ⟨VG.Proof.MlKem.AArch64.Keep.refl _ _,Frame.refl _ _,ha.1.env.x19,ha.1.env.x21,ha.1.table,ha.1.fields⟩
        have ib : BatchInv _ _ (samplerScratch τ) (samplerOut τ) M :=
          ⟨VG.Proof.MlKem.AArch64.Keep.refl _ _,Frame.refl _ _,hd.1.env.x19,hd.1.env.x21,hd.1.table,hd.1.fields⟩
        rw [←hb.scratch,←hb.output] at ly ib
        have e1:=(batch_relCT hη ho lx ly
          (by rw [ha.1.env.sp,hd.1.env.sp]; exact hb.sp) hl hx _ _ _ _ _ _ ⟨ia,ib⟩ es1 et1).1
        exact ⟨by rw [e0,e1],trivial⟩
  exact (ct.wp (fun _ _ h=>⟨sampleRound_ok sha3 hη hp h.1 (by omega),
      sampleRound_ok sha3 hη hq h.2 (by omega)⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourAdaptiveTiming.lean` -/

section

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

end

/-! ## From `BoundedFourEndTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

theorem maskStage_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerBases σ τ) {L M : Nat→List Zq} :
    RelCT isa (fun s t=>(∃A,SamplerRun σ s A L ∧ s.gpr .x27=countFlag L) ∧
      (∃B,SamplerRun τ t B M ∧ t.gpr .x27=countFlag M)) maskFour
      (fun s t=>Sampled σ s L ∧ Sampled τ t M) := by
  obtain ⟨_,hc⟩:=maskFour_taint
  have ct : RelCT isa (fun s t=>(∃A,SamplerRun σ s A L ∧ s.gpr .x27=countFlag L) ∧
      (∃B,SamplerRun τ t B M ∧ t.gpr .x27=countFlag M)) maskFour (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>by
      obtain ⟨⟨A,ha,haf⟩,⟨B,hb',hbf⟩⟩:=h
      apply VG.Proof.MlKem.AArch64.agree_of
      · rw [ha.env.sp,hb'.env.sp]; exact hb.sp
      · intro r hr
        rcases (show r=Reg.x19∨r=Reg.x21 by simpa using hr) with rfl|rfl
        · rw [ha.env.x19,hb'.env.x19]; exact hb.scratch
        · rw [ha.env.x21,hb'.env.x21]; exact hb.output) hc
  exact (ct.wp (fun _ _ h=>by
    obtain ⟨⟨A,ha,haf⟩,⟨B,hb',hbf⟩⟩:=h
    exact ⟨maskStage_ok hp ha haf,maskStage_ok hq hb' hbf⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

theorem finish_relCT {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerBases σ τ) {L M : Nat→List Zq} :
    RelCT isa (fun s t=>Sampled σ s L ∧ Sampled τ t M)
      (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
        Impl.MlDsa.AArch64.Sample.Rej4.epi))
      (fun s t=>Result σ s L ∧ Result τ t M) := by
  obtain ⟨_,hc⟩:=finish_taint
  have ct : RelCT isa (fun s t=>Sampled σ s L ∧ Sampled τ t M)
      (.block (([.subImm .x .x27 .x27 1,.lsr .x .x27 .x27 63] : List Instr)++
        Impl.MlDsa.AArch64.Sample.Rej4.epi)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [h.1.env.sp,h.2.env.sp]; exact hb.sp) (fun r hr=>by
        rw [List.mem_singleton.mp hr,h.1.env.x19,h.2.env.x19]; exact hb.scratch)) hc
  exact (ct.wp (fun _ _ h=>⟨finish_ok hp h.1,finish_ok hq h.2⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>h.2)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure SamplerPublic (η : Nat) (σ τ : State) : Prop extends SamplerBases σ τ where
 seed : samplerSeed σ=samplerSeed τ
 leak : rejBoundedFourLeak η σ.mem (samplerSeed σ)=rejBoundedFourLeak η τ.mem (samplerSeed τ)

theorem setup_relCT {η : Nat} {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ)
    (hb : SamplerPublic η σ τ) :
    RelCT isa (fun s t=>s=σ ∧ t=τ) (.block samplerSetup)
      (fun s t=>SamplerRun σ s (samplerA σ) (fun _=>[]) ∧
        SamplerRun τ t (samplerA τ) (fun _=>[])) := by
  obtain ⟨_,hc⟩:=samplerSetup_taint
  have ct : RelCT isa (fun s t=>s=σ ∧ t=τ) (.block samplerSetup) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>by
      rcases h with ⟨rfl,rfl⟩
      apply VG.Proof.MlKem.AArch64.agree_of hb.sp
      intro r hr
      rcases (show r=Reg.x0∨r=Reg.x1∨r=Reg.x2 by simpa using hr) with rfl|rfl|rfl
      · exact hb.seed
      · exact hb.output
      · exact hb.scratch) hc
  exact (ct.wp (F₁ := Ready σ) (F₂ := Ready τ) (fun _ _ h=>by
    rcases h with ⟨rfl,rfl⟩
    exact ⟨samplerSetup_ok hp,samplerSetup_ok hq⟩)).mono
    (fun _ _ h=>h) (fun _ _ h=>⟨h.2.1.running,h.2.2.running⟩)

/-- All data-dependent parsing and retry decisions are determined by the
original scalar rejection transcript; coefficient values remain secret. -/
theorem sampler_relCT (sha3 : Bool) {η : Nat} (hη : η=2∨η=4)
    {σ τ : State} (hp : SamplerPre σ) (hq : SamplerPre τ) (hb : SamplerPublic η σ τ) :
    RelCT isa (fun s t=>s=σ ∧ t=τ)
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (fun s t=>Result σ s (sampledRows σ η) ∧ Result τ t (sampledRows τ η)) := by
  have h0 := fun i hi=>(fourLeak_chunks hb.leak (i := i) hi).1
  have h1 := fun i hi=>(fourLeak_chunks hb.leak (i := i) hi).2
  have hl : ∀i<4,(rbFold η [] (chunkBytes (samplerA σ i))).length=
      (rbFold η [] (chunkBytes (samplerA τ i))).length := by
    intro i hi
    exact rbFold_length_congr rfl (h0 i hi)
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler
  change RelCT isa _ (.seq (.block samplerSetup) _) _
  apply RelCT.seq (setup_relCT hp hq hb)
  apply RelCT.assoc
  apply RelCT.seq (sampleRound_relCT sha3 hη (Or.inl rfl) hp hq hb.toSamplerBases
    (fun _ _=>rfl) h0)
  apply RelCT.seq (flagsStage_relCT hp hq hb.toSamplerBases)
  change RelCT isa _ (.seq (secondBatch sha3 η) _) _
  apply RelCT.seq (secondBatch_relCT sha3 hη hp hq hb.toSamplerBases hl h1)
  change RelCT isa _ (.seq maskFour _) _
  exact RelCT.seq (maskStage_relCT hp hq hb.toSamplerBases)
    (finish_relCT hp hq hb.toSamplerBases)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourContract.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

def samplerK (η : Nat) : Contract isa where
 pre s := (η=2∨η=4) ∧ SamplerPre s
 post s t := (∀i<4,Reduced t.mem (samplerOut s+BitVec.ofNat 64 (1024*i))) ∧
   (∀i<4,BoundedOutput η t.mem (samplerOut s+BitVec.ofNat 64 (1024*i))) ∧
   Outcome (fun b=>(rejBoundedFour η b.rejBounded s.mem (samplerSeed s)).map (List.map toRq))
     ((t.gpr .x0).setWidth 32)
     ((List.range 4).map fun i=>polyAt t.mem (samplerOut s+BitVec.ofNat 64 (1024*i)))
 pub s t := SamplerPublic η s t

theorem sampler_correct (sha3 : Bool) (η : Nat) (s : State) (h : (samplerK η).pre s) :
    ∃tr t,Exec isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) s tr t ∧
      abiPreserved s t ∧ (samplerK η).post s t := by
  obtain ⟨tr,t,he,ht⟩:=sampler_machine_ok sha3 h.1 h.2
  exact ⟨tr,t,he,ht.abi,(fun i hi=>ht.reduced hi),(fun i hi=>ht.small hi),ht.outcome⟩

theorem sampler_ct (sha3 : Bool) (η : Nat) :
    ConstantTime isa (samplerK η).pre (samplerK η).pub
      (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η) := by
  intro s t tr ur u v hs ht hp es et
  exact (sampler_relCT sha3 hs.1 hs.2 ht.2 hp s t tr ur u v ⟨rfl,rfl⟩ es et).1

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa

theorem sampler_pre (η : Nat) : ∀s,(rejBoundedFourContract abi η).pre s → (samplerK η).pre s := by
  intro s h
  sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at h
  sig_split h
  exact ⟨h,by assumption,by assumption,by assumption,by assumption,by assumption⟩

def samplerSat : State where
 gpr r := if r=.x0 then 4096 else if r=.x1 then 8192 else if r=.x2 then 16384 else 0
 sp := 65536
 mem _ := 0
 rd := [⟨4096,264⟩]
 wr := [⟨8192,4096⟩,⟨16384,8192⟩]

theorem sampler_verified (sha3 : Bool) {η : Nat} (hη : η=2∨η=4) :
    Verified target (Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler sha3 true η)
      (rejBoundedFourContract abi η) := by
  refine Verified.of_correct (sampler_correct sha3 η) (sampler_ct sha3 η)
    { pre := sampler_pre η,post := ?_,pub := ?_,sat := ?_ }
  · sig_implies_post [rejBoundedFourContract,rejBoundedFourSig,samplerK,
      samplerOut,samplerSeed,ResidentRej.aP,ResidentRej.seedP,abi,argRegs]
  · intro s t _ _ h
    sig_pub [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs] at h
    obtain ⟨hsp,hl,h0,h1,h2⟩:=h
    exact ⟨⟨h2,h1,hsp⟩,h0,hl⟩
  · refine ⟨samplerSat,?_⟩
    sig_pre [rejBoundedFourContract,rejBoundedFourSig,abi,argRegs]
    sig_and_intros
    all_goals first | exact hη | rfl | exact Region.disjoint_of_sep (by decide) | decide

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
