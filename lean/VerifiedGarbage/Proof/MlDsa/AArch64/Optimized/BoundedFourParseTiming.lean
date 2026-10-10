import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseAddress
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVectorTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFallback
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse

/-! ## From `BoundedFourParseTrace.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

def parseModel (η k off : Nat) : Prog isa :=
 .seq (.block (parseAddress k off))
   (.seq (parseCore η) (.block [.str .x .x4 .x19 (7904+8*k)]))

/-- Reassociation and splitting a straight-line prefix preserve the exact trace. -/
theorem parse_exec_model {η k off : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η k off) s tr t) :
    Exec isa (parseModel η k off) s tr t := by
  change Exec isa (.seq (.block (parseAddress k off++parseSetup η))
    (.seq (.ite (.zero .x .x8) (.block []) (.loop (.block (vectorBody true η)) (.nonzero .x .x8)))
      (.seq (.block fallbackSetup)
        (.seq (.ite (.zero .x .x8) (.block []) (.loop (scalarLoopBody η) (.nonzero .x .x8)))
          (.block [.str .x .x4 .x19 (7904+8*k)]))))) s tr t at h
  cases h with | seq hp hr =>
    cases hr with | seq hv hr =>
      cases hr with | seq hf hr =>
        cases hr with | seq hs ht =>
          rw [Exec.block_iff,execBlock_append] at hp
          obtain ⟨⟨a,ta⟩,ha,hb⟩:=Option.bind_eq_some_iff.mp hp
          obtain ⟨⟨b,tb⟩,hc,he⟩:=Option.map_eq_some_iff.mp hb
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl,rfl⟩:=he
          have hx : Exec isa (parseModel η k off) s _ t :=
            .seq (.block ha) (.seq (.seq (.block hc) (.seq hv (.seq hf hs))) ht)
          simpa only [List.append_assoc] using hx

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourLoopTiming.lean` -/

section

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

end

/-! ## From `BoundedFourScalarLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

theorem ScalarInv.ready {σ s : State} {η d : Nat} {p q : Addr} {L : List Zq} {X : List Byte}
    (h : ScalarInv σ η p q L X d s) (hy : ScalarLayout σ p q X) (hl : L.length≤256)
    (hd : d<X.length) : ScalarBodyReady η p (parsed η L X d) X[d]! s := by
  refine ⟨h.consts,parsed_bound hl d,h.stored,h.output,h.remaining,?_,?_,?_⟩
  · rw [h.input,h.stream hy hd]
  · rw [h.keep.rd,h.keep.wr,h.input]; exact hy.read d hd
  · intro j hj; rw [h.keep.wr]; exact hy.write j hj

theorem scalarStep_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y)
    (hl : L.length≤256) (hd : d<X.length) :
    RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (scalarLoopBody η)
      (fun s t=>ScalarInv σ η p q L X (d+1) s ∧ ScalarInv τ η p q M Y (d+1) t) := by
  have hm : M.length≤256:=by rw [←h.length]; exact hl
  have hdy : d<Y.length:=by rw [←h.bytes_length]; exact hd
  have cb := (scalarBody_relCT hη (h.parsed_length d) (h.byte hd)).mono
    (fun s t (hh : ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)=>
      ⟨hh.1.ready sx hl hd,hh.2.ready sy hm hdy,
        by rw [hh.1.keep.sp,hh.2.keep.sp]; exact h.sp,
        by rw [hh.1.input,hh.2.input]⟩) (fun _ _ _=>True.intro)
  have cs : RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (VG.Impl.MlDsa.AArch64.Sample.rbBody η) (fun s t=>s.sp=t.sp) := by
    apply RelCT.mono (cb.wp (F₁ := fun (s : State)=>s.sp=σ.sp) (F₂ := fun (t : State)=>t.sp=τ.sp) ?_)
      (fun _ _ hh=>hh) (fun _ _ hh=>by rw [hh.2.1,hh.2.2]; exact h.sp)
    intro s t hh
    have a:=hh.1.ready sx hl hd
    have b:=hh.2.ready sy hm hdy
    exact ⟨WP.mono (scalarBody_ok hη a.consts a.bound a.stored a.output a.remaining a.read a.write)
      (fun _ ht=>ht.keep.sp.trans hh.1.keep.sp),
      WP.mono (scalarBody_ok hη b.consts b.bound b.stored b.output b.remaining b.read b.write)
      (fun _ ht=>ht.keep.sp.trans hh.2.keep.sp)⟩
  have cg : RelCT isa (fun (s t : State)=>s.sp=t.sp)
      (.block [.mul .x .x8 .x4 .x5]) (fun _ _=>True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of hh
        (fun _ hr=>False.elim (List.not_mem_nil hr))) (by taint_decide)
  exact ((RelCT.seq cs cg).wp (fun _ _ hh=>
    ⟨scalarStep_ok hη hl sx hh.1 hd,scalarStep_ok hη hm sy hh.2 hdy⟩)).mono
      (fun _ _ hh=>hh) (fun _ _ hh=>hh.2)

def ScalarPairDone (σ τ : State) (η : Nat) (p q : Addr)
    (L M : List Zq) (X Y : List Byte) (s t : State) : Prop :=
 ∃d,ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t ∧
   (d=X.length ∨ (parsed η L X d).length=256)

theorem scalarLoop_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y)
    (hL0 : L.length≤256) (hd : d<X.length)
    (hl : (parsed η L X d).length<256) :
    RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (.loop (scalarLoopBody η) (.nonzero .x .x8))
      (ScalarPairDone σ τ η p q L M X Y) := by
  let I := fun rank s t=>∃j,rank=X.length-j ∧
    ScalarInv σ η p q L X j s ∧ ScalarInv τ η p q M Y j t ∧
    j<X.length ∧ (parsed η L X j).length<256
  have step (rank : Nat) : RelCT isa (I rank) (scalarLoopBody η)
      (fun s t=>isa.eval (.nonzero .x .x8) s=isa.eval (.nonzero .x .x8) t ∧
        (isa.eval (.nonzero .x .x8) s=some false→ScalarPairDone σ τ η p q L M X Y s t) ∧
        (isa.eval (.nonzero .x .x8) s=some true→∃m<rank,I m s t)) := by
    intro s t a b u v hp es et
    obtain ⟨j,rfl,hs,ht,hj,hL⟩:=hp
    obtain ⟨he,hu,hv⟩:=scalarStep_relCT hη h sx sy hL0 hj _ _ _ _ _ _ ⟨hs,ht⟩ es et
    have eu:=scalarGuard_nonzero hL0 sx hu
    have ev:=scalarGuard_nonzero (by rw [←h.length]; exact hL0) sy hv
    have ee : isa.eval (.nonzero .x .x8) u=isa.eval (.nonzero .x .x8) v := by
      rw [eu,ev,h.bytes_length,h.parsed_length]
    refine ⟨he,ee,?_,?_⟩
    · intro hz
      rw [eu] at hz
      have hn : ¬(j+1<X.length ∧ (parsed η L X (j+1)).length<256) := by
        simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
      exact ⟨j+1,hu,hv,by have:=hu.bound; have:=parsed_bound (η := η) (X := X) hL0 (j+1); omega⟩
    · intro hn
      rw [eu] at hn
      have hc : j+1<X.length ∧ (parsed η L X (j+1)).length<256 := by
        simpa only [Option.some.injEq,decide_eq_true_eq] using hn
      exact ⟨X.length-(j+1),by omega,j+1,rfl,hu,hv,hc⟩
  exact (RelCT.loop I step (X.length-d)).mono
    (fun _ _ hh=>⟨d,rfl,hh.1,hh.2,hd,hl⟩) (fun _ _ hh=>hh)

theorem scalarPhase_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y)
    (hL0 : L.length≤256) :
    RelCT isa
      (fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
      (.ite (.zero .x .x8) (.block [])
        (.loop (scalarLoopBody η) (.nonzero .x .x8)))
      (ScalarPairDone σ τ η p q L M X Y) := by
  refine RelCT.ite (fun s t hh=>by
    rw [scalarGuard_zero hL0 sx hh.1,scalarGuard_zero (by rw [←h.length]; exact hL0) sy hh.2,
      h.bytes_length,h.parsed_length]) ?_ ?_
  · intro s t a b u v hh es et
    have he : s=u ∧ a=[] := by
      cases es with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    have hf : t=v ∧ b=[] := by
      cases et with | block he => simp only [execBlock] at he; cases he; exact ⟨rfl,rfl⟩
    obtain ⟨rfl,rfl⟩:=he
    obtain ⟨rfl,rfl⟩:=hf
    have hz:=hh.2
    rw [scalarGuard_zero hL0 sx hh.1.1] at hz
    exact ⟨rfl,d,hh.1.1,hh.1.2,by
      simpa only [Option.some.injEq,decide_eq_true_eq] using hz⟩
  · intro s t a b u v hh es et
    have hz:=hh.2
    rw [scalarGuard_zero hL0 sx hh.1.1] at hz
    have hn : ¬(d=X.length ∨ (parsed η L X d).length=256) := by
      simpa only [Option.some.injEq,decide_eq_false_iff_not] using hz
    have hd : d<X.length:=by have:=hh.1.1.bound; omega
    exact scalarLoop_relCT hη h sx sy hL0 hd (by have:=parsed_bound (η := η) (X := X) hL0 d; omega) _ _ _ _ _ _ hh.1 es et

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourParserTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

theorem fallback_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y) (hL : L.length≤256) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (fallback η) (ScalarPairDone σ τ η p q L M X Y) := by
  unfold fallback
  refine RelCT.seq (R := fun s t=>ScalarInv σ η p q L X d s ∧ ScalarInv τ η p q M Y d t)
    ?_ (scalarPhase_relCT hη h sx sy hL)
  have hc : ∃hint,(taint.check (Taint.ofRegs []) (.block fallbackSetup) hint).isSome=true:=⟨_,by taint_decide⟩
  obtain ⟨_,hc⟩:=hc
  have ct : RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.block fallbackSetup) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of
      (by rw [hh.1.keep.sp,hh.2.keep.sp]; exact h.sp)
      (fun _ hr=>False.elim (List.not_mem_nil hr))) hc
  exact (ct.wp (fun _ _ hh=>⟨fallbackSetup_inv hh.1,fallbackSetup_inv hh.2⟩)).mono
    (fun _ _ hh=>hh) (fun _ _ hh=>hh.2)

/-- All vector lookups, scalar stores, and both adaptive parser exits are
fixed by the standard bounded-sampler rejection transcript. -/
theorem parsedPhase_relCT {σ τ : State} {η d : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L M : List Zq} {X Y : List Byte}
    (h : TranscriptPair σ τ η table p q L M X Y)
    (sx : ScalarLayout σ p q X) (sy : ScalarLayout τ p q Y) (hL : L.length≤256) :
    RelCT isa
      (fun s t=>LoopInv σ η table p q L X d s ∧ LoopInv τ η table p q M Y d t)
      (.seq (.ite (.zero .x .x8) (.block [])
        (.loop (.block (vectorBody true η)) (.nonzero .x .x8))) (fallback η))
      (ScalarPairDone σ τ η p q L M X Y) := by
  refine RelCT.seq (vectorPhase_relCT hη h) ?_
  apply RelCT.mono (RelCT.exists_ (fun j=>fallback_relCT (d := j) hη h sx sy hL))
  · intro s t hh
    obtain ⟨j,hs,ht,_⟩:=hh
    exact ⟨j,hs,ht⟩
  · intro _ _ hh; exact hh

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourCoreTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure CoreReady (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte) (s : State) : Prop where
 bound : L.length≤256
 bytes : X.length=272
 vectorLayout : Layout s table p q X
 scalarLayout : ScalarLayout s p q X
 tableMem : TableAt s.mem table
 stored : Stored s.mem p L
 input : s.gpr .x2=q
 output : s.gpr .x3=p
 count : s.gpr .x4=BitVec.ofNat 64 (256-L.length)
 tableAddr : s.gpr .x19+6000=table

theorem parseSetup_taint {η : Nat} (hη : η=2∨η=4) : ∃hint,
    (taint.check (Taint.ofRegs []) (.block (parseSetup η)) hint).isSome=true :=
  by rcases hη with rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem parseCore_relCT {η : Nat} (hη : η=2∨η=4) {table p q : Addr}
    {L M : List Zq} {X Y : List Byte} (hl : L.length=M.length)
    (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>CoreReady η table p q L X s ∧ CoreReady η table p q M Y t ∧ s.sp=t.sp)
      (parseCore η) (fun _ _=>True) := by
  obtain ⟨_,hc⟩:=parseSetup_taint hη
  have cs : RelCT isa (fun s t=>s.sp=t.sp) (.block (parseSetup η)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ hh=>VG.Proof.MlKem.AArch64.agree_of hh
      (fun _ hr=>False.elim (List.not_mem_nil hr))) hc
  intro s t tr ur u v h es et
  cases es with | seq es0 es1 =>
    cases et with | seq et0 et1 =>
      have he:=(cs _ _ _ _ _ _ h.2.2 es0 et0).1
      obtain ⟨_,_,ex,ha⟩:=parseSetup_inv hη h.1.bound h.1.bytes h.1.tableMem h.1.stored
        h.1.input h.1.output h.1.count h.1.tableAddr
      obtain ⟨_,_,ey,hb⟩:=parseSetup_inv hη h.2.1.bound h.2.1.bytes h.2.1.tableMem h.2.1.stored
        h.2.1.input h.2.1.output h.2.1.count h.2.1.tableAddr
      obtain ⟨_,rfl⟩:=Exec.det es0 ex
      obtain ⟨_,rfl⟩:=Exec.det et0 ey
      have hp : TranscriptPair _ _ η table p q L M X Y :=
        ⟨h.1.vectorLayout.keep ha.1 ha.2.1,h.2.1.vectorLayout.keep hb.1 hb.2.1,
          by rw [ha.1.sp,hb.1.sp]; exact h.2.2,hl,hx⟩
      have ht:=(parsedPhase_relCT hη hp
        (h.1.scalarLayout.keep ha.1 ha.2.1) (h.2.1.scalarLayout.keep hb.1 hb.2.1)
        h.1.bound _ _ _ _ _ _ ⟨ha.2.2,hb.2.2⟩ es1 et1).1
      exact ⟨by rw [he,ht],trivial⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourParseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample

structure ParseReady (k off : Nat) (table p q a : Addr) (L : List Zq) (X : List Byte) (s : State) : Prop where
 bound : L.length≤256
 bytes : X.length=272
 vectorLayout : Layout s table p q X
 scalarLayout : ScalarLayout s p q X
 tableMem : TableAt s.mem table
 stored : Stored s.mem p L
 input : s.gpr .x19+BitVec.ofNat 64 (840+544*k+off)=q
 output : s.gpr .x21+BitVec.ofNat 64 (1024*k)=p
 countAddr : s.gpr .x19+BitVec.ofNat 64 (7904+8*k)=a
 tableAddr : s.gpr .x19+6000=table
 count : s.mem.readW a 64=BitVec.ofNat 64 (256-L.length)
 read : InRegions (s.rd++s.wr) a 8

theorem parseAddress_ready {η k off : Nat} (hk : k<4) (ho : off≤272)
    {table p q a : Addr} {L : List Zq} {X : List Byte} {s : State}
    (h : ParseReady k off table p q a L X s) :
    WP isa (.block (parseAddress k off)) s fun t=>
      VG.Proof.MlKem.AArch64.Only [.x2,.x3,.x4] s t ∧ CoreReady η table p q L X t := by
  refine WP.mono (parseAddress_ok hk ho (by rw [h.countAddr]; exact h.read)) fun t ⟨ht,h2,h3,h4⟩=>?_
  refine ⟨ht,h.bound,h.bytes,h.vectorLayout.keep ht.keep ht.mem,
    h.scalarLayout.keep ht.keep ht.mem,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.mem]; exact h.tableMem
  · rw [ht.mem]; exact h.stored
  · rw [h2]; exact h.input
  · rw [h3]; exact h.output
  · rw [h4,h.countAddr,h.count]
  · rw [ht.get .x19]; exact h.tableAddr

theorem parseAddress_taint {k off : Nat} (hk : k<4) (ho : off=0∨off=272) : ∃h,
    (taint.check (Taint.ofRegs [.x19,.x21]) (.block (parseAddress k off)) h).isSome=true := by
  rcases (show k=0∨k=1∨k=2∨k=3 by omega) with rfl|rfl|rfl|rfl <;>
    rcases ho with rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem parseStore_taint {k : Nat} (hk : k<4) : ∃h,
    (taint.check (Taint.ofRegs [.x19]) (.block [.str .x .x4 .x19 (7904+8*k)]) h).isSome=true := by
  rcases (show k=0∨k=1∨k=2∨k=3 by omega) with rfl|rfl|rfl|rfl <;> exact ⟨_,by taint_decide⟩

theorem parseModel_relCT {η k off : Nat} (hη : η=2∨η=4) (hk : k<4) (ho : off=0∨off=272)
    {table p q a : Addr} {L M : List Zq} {X Y : List Byte}
    (hl : L.length=M.length) (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>ParseReady k off table p q a L X s ∧ ParseReady k off table p q a M Y t ∧
      s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19 ∧ s.gpr .x21=t.gpr .x21)
      (parseModel η k off) (fun _ _=>True) := by
  obtain ⟨_,ha⟩:=parseAddress_taint hk ho
  obtain ⟨_,hz⟩:=parseStore_taint hk
  have ca : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19 ∧ s.gpr .x21=t.gpr .x21)
      (.block (parseAddress k off)) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact h.2.1
      · exact h.2.2)) ha
  have cz : RelCT isa (fun (s t : State)=>s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19)
      (.block [.str .x .x4 .x19 (7904+8*k)]) (fun _ _=>True) :=
    RelCT.taint (A := taint) _ (fun _ _ h=>VG.Proof.MlKem.AArch64.agree_of h.1 (fun r hr=>by
      rw [List.mem_singleton.mp hr]; exact h.2)) hz
  intro s t tr ur u v h es et
  cases es with | seq es0 es1 =>
    cases es1 with | seq es1 es2 =>
      cases et with | seq et0 et1 =>
        cases et1 with | seq et1 et2 =>
          have e0:=(ca _ _ _ _ _ _ h.2.2 es0 et0).1
          obtain ⟨_,_,ex,sa⟩:=parseAddress_ready (η := η) hk (by omega) h.1
          obtain ⟨_,_,ey,ta⟩:=parseAddress_ready (η := η) hk (by omega) h.2.1
          obtain ⟨_,rfl⟩:=Exec.det es0 ex
          obtain ⟨_,rfl⟩:=Exec.det et0 ey
          have hs : _ := sa.2
          have ht : _ := ta.2
          have hsp : _ := sa.1.sp.trans (h.2.2.1.trans ta.1.sp.symm)
          have e1:=(parseCore_relCT hη hl hx _ _ _ _ _ _ ⟨hs,ht,hsp⟩ es1 et1).1
          obtain ⟨_,_,ex,hb⟩:=parseCore_ok hη hs.bound hs.bytes hs.vectorLayout hs.scalarLayout
            hs.tableMem hs.stored hs.input hs.output hs.count hs.tableAddr
          obtain ⟨_,_,ey,hc⟩:=parseCore_ok hη ht.bound ht.bytes ht.vectorLayout ht.scalarLayout
            ht.tableMem ht.stored ht.input ht.output ht.count ht.tableAddr
          obtain ⟨_,rfl⟩:=Exec.det es1 ex
          obtain ⟨_,rfl⟩:=Exec.det et1 ey
          have e2:=(cz _ _ _ _ _ _ ⟨by rw [hb.1.sp,hc.1.sp]; exact hsp,
            by rw [hb.1.gpr .x19 (by decide),hc.1.gpr .x19 (by decide),sa.1.get .x19,ta.1.get .x19]; exact h.2.2.2.1⟩ es2 et2).1
          exact ⟨by rw [e0,e1,e2],trivial⟩

theorem parse_relCT {η k off : Nat} (hη : η=2∨η=4) (hk : k<4) (ho : off=0∨off=272)
    {table p q a : Addr} {L M : List Zq} {X Y : List Byte}
    (hl : L.length=M.length) (hx : X.map (hbOks η)=Y.map (hbOks η)) :
    RelCT isa (fun s t=>ParseReady k off table p q a L X s ∧ ParseReady k off table p q a M Y t ∧
      s.sp=t.sp ∧ s.gpr .x19=t.gpr .x19 ∧ s.gpr .x21=t.gpr .x21)
      (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.parse true η k off) (fun _ _=>True) := by
  intro _ _ _ _ _ _ h es et
  exact parseModel_relCT hη hk ho hl hx _ _ _ _ _ _ h (parse_exec_model es) (parse_exec_model et)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
