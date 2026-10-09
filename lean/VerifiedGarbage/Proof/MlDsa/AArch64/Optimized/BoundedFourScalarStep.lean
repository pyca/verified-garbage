import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarState

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
