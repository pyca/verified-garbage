import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarLoop

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
