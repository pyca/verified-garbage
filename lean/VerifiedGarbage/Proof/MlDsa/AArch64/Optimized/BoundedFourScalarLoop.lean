import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarStep

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def ScalarDone (σ : State) (η : Nat) (p q : Addr) (L : List Zq) (X : List Byte)
    (s : State) : Prop := ∃done,ScalarInv σ η p q L X done s ∧
      (done=X.length ∨ (parsed η L X done).length=256)

def scalarLoopBody (η : Nat) : Prog isa :=
 .seq (VG.Impl.MlDsa.AArch64.Sample.rbBody η) (.block [.mul .x .x8 .x4 .x5])

theorem scalarGuard_nonzero {σ s : State} {η done : Nat} {p q : Addr}
    {L : List Zq} {X : List Byte} (hl : L.length≤256) (hy : ScalarLayout σ p q X)
    (hi : ScalarInv σ η p q L X done s) :
    isa.eval (.nonzero .x .x8) s=some (decide (done<X.length ∧ (parsed η L X done).length<256)) := by
  have hr : 256-(parsed η L X done).length≤256 := Nat.sub_le _ _
  have hn : X.length-done≤272 := by have:=hy.short; omega
  have hp : (256-(parsed η L X done).length)*(X.length-done)<2^64 := by
    have:=Nat.mul_le_mul hr hn
    omega
  rw [eval_nonzero,hi.guard,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
  congr 1
  apply decide_eq_decide.mpr
  rw [Nat.mul_ne_zero_iff]
  have:=hi.bound
  have:=parsed_bound (η := η) (X := X) hl done
  omega

theorem scalarGuard_zero {σ s : State} {η done : Nat} {p q : Addr}
    {L : List Zq} {X : List Byte} (hl : L.length≤256) (hy : ScalarLayout σ p q X)
    (hi : ScalarInv σ η p q L X done s) :
    isa.eval (.zero .x .x8) s=some (decide (done=X.length ∨ (parsed η L X done).length=256)) := by
  have hn:=scalarGuard_nonzero hl hy hi
  rw [eval_nonzero] at hn
  rw [eval_zero]
  have h : (s.gpr .x8 != 0)=decide (done<X.length ∧ (parsed η L X done).length<256) := Option.some.inj hn
  have hb:=parsed_bound (η := η) (X := X) hl done
  have hd:=hi.bound
  by_cases he : done=X.length ∨ (parsed η L X done).length=256
  · have hn : ¬(done<X.length ∧ (parsed η L X done).length<256) := by omega
    simp only [decide_eq_false hn] at h
    have hz : s.gpr .x8=0 := by simpa using h
    simp [hz,he]
  · have hn : done<X.length ∧ (parsed η L X done).length<256 := by omega
    simp only [decide_eq_true hn] at h
    have hz : s.gpr .x8≠0 := by simpa using h
    simp only [decide_eq_false he,Option.some.injEq,beq_eq_false_iff_ne]
    exact hz

theorem scalarLoop_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hy : ScalarLayout σ p q X) (hi : ScalarInv σ η p q L X done s)
    (hd : done<X.length) (hn : (parsed η L X done).length<256) :
    WP isa (.loop (scalarLoopBody η) (.nonzero .x .x8)) s (ScalarDone σ η p q L X) := by
  refine WP.loop (M := isa)
    (fun rank s=>∃d,rank=X.length-d ∧ ScalarInv σ η p q L X d s ∧
      d<X.length ∧ (parsed η L X d).length<256) ?_ (X.length-done) s
    ⟨done,rfl,hi,hd,hn⟩
  rintro rank u ⟨d,rfl,hu,hd,hn⟩
  refine WP.mono (scalarStep_ok hη hl hy hu hd) fun v hv=>?_
  have he:=scalarGuard_nonzero hl hy hv
  by_cases hc : d+1<X.length ∧ (parsed η L X (d+1)).length<256
  · exact .inr ⟨by rw [he,decide_eq_true hc],X.length-(d+1),by omega,d+1,rfl,hv,hc⟩
  · refine .inl ⟨by rw [he,decide_eq_false hc],d+1,hv,?_⟩
    have:=hv.bound
    have:=parsed_bound (η := η) (X := X) hl (d+1)
    omega

theorem scalarPhase_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hy : ScalarLayout σ p q X) (hi : ScalarInv σ η p q L X done s) :
    WP isa (.ite (.zero .x .x8) (.block [])
      (.loop (scalarLoopBody η) (.nonzero .x .x8))) s (ScalarDone σ η p q L X) := by
  have he:=scalarGuard_zero hl hy hi
  by_cases hc : done=X.length ∨ (parsed η L X done).length=256
  · exact WP.ite true (by rw [he,decide_eq_true hc])
      (fun _=>WP.block_nil_iff.mpr ⟨done,hi,hc⟩) (fun h=>nomatch h)
  · exact WP.ite false (by rw [he,decide_eq_false hc]) (fun h=>nomatch h)
      (fun _=>scalarLoop_ok hη hl hy hi (by have:=hi.bound; omega)
        (by have:=parsed_bound (η := η) (X := X) hl done; omega))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
