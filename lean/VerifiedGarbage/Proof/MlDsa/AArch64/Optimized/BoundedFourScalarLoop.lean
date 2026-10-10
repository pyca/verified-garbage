import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTraversal

/-! ## From `BoundedFourScalarBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Sample (rbBody)

def scalarRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x12,.x13,.x14]

structure ScalarBodyPost (η : Nat) (s t : State) (p : Addr) (L : List Zq) : Prop where
 keep : Keep scalarRegs s t
 frame : Frame [polyR p] s.mem t.mem
 input : t.gpr .x2=s.gpr .x2+1
 bytes : t.gpr .x5=s.gpr .x5-1
 output : t.gpr .x3=coeffAddr p (rbStep η L (s.mem (s.gpr .x2))).length
 remaining : (t.gpr .x4).toNat=256-(rbStep η L (s.mem (s.gpr .x2))).length
 stored : Stored t.mem p (rbStep η L (s.mem (s.gpr .x2)))

theorem scalarBody_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr} {L : List Zq}
    (hC : ScalarConsts η s) (hL : L.length≤256) (hS : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (hR : InRegions (s.rd++s.wr) (s.gpr .x2) 1)
    (hW : ∀j<256,InRegions s.wr (coeffAddr p j) 4) :
    WP isa (rbBody η) s fun t=>ScalarBodyPost η s t p L := by
  change WP isa (.seq (.block VG.Impl.MlDsa.AArch64.Sample.rbLoad) (scalarPair η)) s _
  refine WP.seq (WP.mono (scalarLoad_ok hC.x11 hR) fun a ⟨hak,ha2,ha5,ha6,ha7⟩=>?_
    )
  refine WP.mono (scalarPair_ok hη (hC.keep hak.keep (by decide)) hL
    (by rw [hak.mem]; exact hS)
    (by rw [hak.get .x3]; exact h3) (by rw [hak.get .x4]; exact h4) ha6 ha7
    (fun j hj=>by rw [hak.wr]; exact hW j hj)) fun t ht=>?_
  refine ⟨(hak.keep.trans ht.keep).mono (by decide),?_,?_,?_,ht.output,ht.remaining,ht.stored⟩
  · rw [←hak.mem]; exact ht.frame
  · rw [ht.keep.gpr .x2 (by decide),ha2]
  · rw [ht.keep.gpr .x5 (by decide),ha5]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def parserRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

structure ScalarLayout (σ : State) (p q : Addr) (X : List Byte) : Prop where
 short : X.length≤272
 stream : ∀i<X.length,σ.mem (q+BitVec.ofNat 64 i)=X[i]!
 apart : (⟨q,X.length⟩ : Region).Disjoint (polyR p)
 read : ∀i<X.length,InRegions (σ.rd++σ.wr) (q+BitVec.ofNat 64 i) 1
 write : ∀j<256,InRegions σ.wr (coeffAddr p j) 4

structure ScalarInv (σ : State) (η : Nat) (p q : Addr) (L : List Zq) (X : List Byte)
    (done : Nat) (s : State) : Prop where
 bound : done≤X.length
 consts : ScalarConsts η s
 keep : Keep parserRegs σ s
 frame : Frame [polyR p] σ.mem s.mem
 stored : Stored s.mem p (parsed η L X done)
 input : s.gpr .x2=q+BitVec.ofNat 64 done
 output : s.gpr .x3=coeffAddr p (parsed η L X done).length
 remaining : (s.gpr .x4).toNat=256-(parsed η L X done).length
 bytes : s.gpr .x5=BitVec.ofNat 64 (X.length-done)
 guard : s.gpr .x8=BitVec.ofNat 64 ((256-(parsed η L X done).length)*(X.length-done))

theorem ScalarInv.stream {σ s : State} {η done : Nat} {p q : Addr} {L : List Zq} {X : List Byte}
    (h : ScalarInv σ η p q L X done s) (hy : ScalarLayout σ p q X) {i : Nat} (hi : i<X.length) :
    s.mem (q+BitVec.ofNat 64 i)=X[i]! := by
  rw [h.frame.bytes (R := ⟨q,X.length⟩) (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact hy.apart) (by change X.length≤2^64; have:=hy.short; omega) hi]
  exact hy.stream i hi

theorem scalarGuard_ok {s : State} {r n : Nat}
    (h4 : (s.gpr .x4).toNat=r) (h5 : s.gpr .x5=BitVec.ofNat 64 n) :
    WP isa (.block [.mul .x .x8 .x4 .x5]) s fun t=>
      Only [.x8] s t ∧ t.gpr .x8=BitVec.ofNat 64 (r*n) := by
  have hh : s.gpr .x4=BitVec.ofNat 64 r := by rw [←h4]; simp
  refine wp_mul fun t ht he=>wp_nil ⟨ht,?_⟩
  rw [he,hh,h5,BitVec.ofNat_mul]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

theorem scalarStep_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hy : ScalarLayout σ p q X) (hi : ScalarInv σ η p q L X done s) (hd : done<X.length) :
    WP isa (.seq (VG.Impl.MlDsa.AArch64.Sample.rbBody η)
      (.block [.mul .x .x8 .x4 .x5])) s
      (ScalarInv σ η p q L X (done+1)) := by
  have hb := parsed_bound hl done (X := X) (η := η)
  have he : rbStep η (parsed η L X done) (s.mem (s.gpr .x2))=parsed η L X (done+1) := by
    rw [hi.input,hi.stream hy hd,parsed_one hd]
  refine WP.seq (WP.mono (scalarBody_ok hη hi.consts hb hi.stored hi.output hi.remaining
    (by rw [hi.input,hi.keep.rd,hi.keep.wr]; exact hy.read done hd)
    (fun j hj=>by rw [hi.keep.wr]; exact hy.write j hj)) fun t ht=>?_)
  rcases ht with ⟨htkeep,htframe,htinput,htbytes,htoutput,htremaining,htstored⟩
  rw [he] at htoutput htremaining htstored
  have ht5 : t.gpr .x5=BitVec.ofNat 64 (X.length-(done+1)) := by
    rw [htbytes,hi.bytes]
    have hh:=BitVec.ofNat_sub_ofNat_of_le (w := 64) (X.length-done) 1 (by decide) (by omega)
    change BitVec.ofNat 64 (X.length-done)-1#64=_
    simpa only [show X.length-done-1=X.length-(done+1) by omega] using hh
  refine WP.mono (scalarGuard_ok htremaining ht5) fun u ⟨hu,h8⟩=>?_
  have hk : Keep parserRegs σ u :=
    ((hi.keep.trans htkeep).trans hu.keep).mono (by decide)
  refine ⟨by omega,(hi.consts.keep htkeep (by decide)).keep hu.keep (by decide),hk,?_,?_,?_,?_,?_,?_,h8⟩
  · rw [hu.mem]; exact hi.frame.trans htframe
  · rw [hu.mem]; exact htstored
  · rw [hu.get .x2,htinput,hi.input,BitVec.add_assoc,BitVec.ofNat_add]
    rfl
  · rw [hu.get .x3]; exact htoutput
  · rw [hu.get .x4]; exact htremaining
  · rw [hu.get .x5]; exact ht5

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarLoop.lean` -/

section

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

end
