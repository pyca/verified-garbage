import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatch

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
