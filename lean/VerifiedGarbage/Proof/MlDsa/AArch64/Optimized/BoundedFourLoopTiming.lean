import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVectorTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

structure TranscriptPair (σ τ : State) (η : Nat) (table p q : Addr)
    (L M : List Zq) (X Y : List Byte) : Prop where
 left : Layout σ table p q X
 right : Layout τ table p q Y
 sp : σ.sp=τ.sp
 length : L.length=M.length
 bytes : X.map (hbOks η)=Y.map (hbOks η)

theorem TranscriptPair.bytes_length {σ τ : State} {η : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y) :
    X.length=Y.length := by
  simpa only [List.length_map] using congrArg List.length h.bytes

theorem TranscriptPair.parsed_length {σ τ : State} {η : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y) (d : Nat) :
    (parsed η L X d).length=(parsed η M Y d).length :=
  transcript_prefix_length h.bytes h.length d

theorem TranscriptPair.byte {σ τ : State} {η : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y)
    {i : Nat} (hi : i<X.length) : hbOks η X[i]! =hbOks η Y[i]! := by
  have hy : i<Y.length:=by rw [←h.bytes_length]; exact hi
  have hh:=congrArg (fun Z : List (Nat×Nat)=>Z[i]!) h.bytes
  simpa only [getElem!_pos (X.map (hbOks η)) i (by simpa using hi),
    getElem!_pos (Y.map (hbOks η)) i (by simpa using hy),List.getElem_map,
    getElem!_pos X i hi,getElem!_pos Y i hy] using hh

theorem loopInv_public {σ τ s t : State} {η d : Nat} {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (h : TranscriptPair σ τ η table p q L M X Y)
    (hs : LoopInv σ η table p q L X d s) (ht : LoopInv τ η table p q M Y d t)
    (hd : d+2≤X.length) : VectorPublic η s t := by
  have hdY : d+2≤Y.length:=by rw [←h.bytes_length]; exact hd
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hs.consts.table]; exact hs.consts
  · rw [ht.consts.table]; exact ht.consts
  · rw [hs.keep.rd,hs.keep.wr,hs.input]; exact h.left.read d hd
  · rw [ht.keep.rd,ht.keep.wr,ht.input]; exact h.right.read d hdY
  · rw [hs.keep.sp,ht.keep.sp]; exact h.sp
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · rw [hs.input,ht.input]
    · rw [hs.output,ht.output,h.parsed_length]
    · rw [hs.consts.table,ht.consts.table]
  · rw [hs.input,ht.input,hs.stream h.left (by omega),ht.stream h.right (by omega)]
    exact h.byte (by omega)
  · have ea : q+BitVec.ofNat 64 d+1=q+BitVec.ofNat 64 (d+1) := by
      rw [BitVec.add_assoc,BitVec.ofNat_add]; rfl
    rw [hs.input,ht.input,ea,hs.stream h.left (by omega),ht.stream h.right (by omega)]
    exact h.byte (by omega)

theorem vectorLoopStep_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y) (hd : d+2≤X.length)
    (hl : (parsed η L X d).length≤252) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.block (vectorBody true η))
      (fun s t=>LoopInv σ η table p q L X (d+2) s ∧ LoopInv τ η table p q M Y (d+2) t) := by
  have hc:=RelCT.mono (vectorBody_relCT hη)
    (fun s t (hh : LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)=>
      loopInv_public h hh.1 hh.2 hd) (fun _ _ _=>True.intro)
  exact (hc.wp (fun s t hh=>
    ⟨vectorLoopStep_ok hη h.left hh.1 hd hl,
     vectorLoopStep_ok hη h.right hh.2 (by rw [←h.bytes_length]; exact hd)
       (by rw [←h.parsed_length]; exact hl)⟩)).mono
         (fun _ _ hh=>hh) (fun _ _ hh=>hh.2)

def VectorPairDone (σ τ : State) (η : Nat) (table p q : Addr)
    (L M : List Zq) (X Y : List Byte) (s t : State) : Prop :=
 ∃d,LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t ∧
   (d=X.length ∨ 252<(parsed η L X d).length)

theorem vectorLoop_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y) (hd : d<X.length)
    (hl : (parsed η L X d).length≤252) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.loop (.block (vectorBody true η)) (.nonzero .x .x8))
      (VectorPairDone σ τ η table p q L M X Y) := by
  let I := fun rank s t=>∃j,rank=X.length-j ∧
    LoopInv σ η table p q L X j s ∧ LoopInv τ η table p q M Y j t ∧
    j<X.length ∧ (parsed η L X j).length≤252
  have step (rank : Nat) : RelCT isa (I rank) (.block (vectorBody true η))
      (fun s t=>isa.eval (.nonzero .x .x8) s=isa.eval (.nonzero .x .x8) t ∧
        (isa.eval (.nonzero .x .x8) s=some false→VectorPairDone σ τ η table p q L M X Y s t) ∧
        (isa.eval (.nonzero .x .x8) s=some true→∃m<rank,I m s t)) := by
    intro s t a b u v hp es et
    obtain ⟨j,rfl,hs,ht,hj,hL⟩:=hp
    have hj2 : j+2≤X.length:=by have:=h.left.even; have:=hs.even; omega
    obtain ⟨he,hu,hv⟩:=vectorLoopStep_relCT hη h hj2 hL _ _ _ _ _ _ ⟨hs,ht⟩ es et
    have eu:=loopGuard_eval h.left hu
    have ev:=loopGuard_eval h.right hv
    have ee : isa.eval (.nonzero .x .x8) u=isa.eval (.nonzero .x .x8) v := by
      rw [eu,ev,h.bytes_length,h.parsed_length]
    refine ⟨he,ee,?_,?_⟩
    · intro hz
      rw [eu] at hz
      have hn : ¬(j+2<X.length ∧ (parsed η L X (j+2)).length≤252) := by
        simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
      exact ⟨j+2,hu,hv,by have:=hu.bound; omega⟩
    · intro hn
      rw [eu] at hn
      have hc : j+2<X.length ∧ (parsed η L X (j+2)).length≤252 := by
        simpa only [Option.some.injEq,decide_eq_true_eq] using hn
      exact ⟨X.length-(j+2),by omega,j+2,rfl,hu,hv,hc⟩
  exact (RelCT.loop I step (X.length-d)).mono
    (fun _ _ hh=>⟨d,rfl,hh.1,hh.2,hd,hl⟩) (fun _ _ hh=>hh)

theorem vectorPhase_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.ite (.zero .x .x8) (.block [])
        (.loop (.block (vectorBody true η)) (.nonzero .x .x8)))
      (VectorPairDone σ τ η table p q L M X Y) := by
  refine RelCT.ite (fun s t hh=>by
    rw [loopGuard_zero h.left hh.1,loopGuard_zero h.right hh.2,
      h.bytes_length,h.parsed_length]) ?_ ?_
  · intro s t a b u v hh es et
    have he : s=u ∧ a=[] := by
      cases es with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    have hf : t=v ∧ b=[] := by
      cases et with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    obtain ⟨rfl,rfl⟩:=he
    obtain ⟨rfl,rfl⟩:=hf
    have hz:=hh.2
    rw [loopGuard_zero h.left hh.1.1] at hz
    exact ⟨rfl,d,hh.1.1,hh.1.2,by
      simpa only [Option.some.injEq,decide_eq_true_eq] using hz⟩
  · intro s t a b u v hh es et
    have hz:=hh.2
    rw [loopGuard_zero h.left hh.1.1] at hz
    have hn : ¬(d=X.length ∨ 252<(parsed η L X d).length) := by
      simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
    have hd : d<X.length:=by have:=hh.1.1.bound; omega
    exact vectorLoop_relCT hη h hd (by omega) _ _ _ _ _ _ hh.1 es et

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
