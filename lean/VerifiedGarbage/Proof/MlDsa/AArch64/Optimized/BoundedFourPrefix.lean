import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourExtractMachine
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSelect

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep VChg)

def sourceNibble (s : State) (e : Nat) : Nat := (nibbleWord (s.v .v0) e).toNat

def sourceMask (η : Nat) (s : State) : Nat :=
 nibbleMask η (sourceNibble s 0) (sourceNibble s 1) (sourceNibble s 2) (sourceNibble s 3)

def sourceValues (η : Nat) (s : State) : List Spec.MlDsa.Zq :=
 accepted η [sourceNibble s 0,sourceNibble s 1,sourceNibble s 2,sourceNibble s 3]

theorem sourceMask_lt (η : Nat) (s : State) : sourceMask η s<16 := nibbleMask_lt _ _ _ _ _

theorem sourceValues_length (η : Nat) (s : State) : (sourceValues η s).length≤4 :=
 accepted_length _ _

theorem sourceMask_count (η : Nat) (s : State) :
    (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.acceptedIndices (sourceMask η s)).length=
      (sourceValues η s).length := selected_count _ _ _ _ _

theorem sourceValues_lane (η : Nat) (s : State) {i : Nat}
    (hi : i<(VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.acceptedIndices (sourceMask η s)).length) :
    Spec.MlDsa.ofInt (VG.Proof.MlDsa.Sample.rbC η
      (sourceNibble s ((VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.acceptedIndices (sourceMask η s))[i]!)))=
      (sourceValues η s).getD i 0 := by
  let ids:=VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.acceptedIndices (sourceMask η s)
  have hn : ids[i]!<4:=index_bound (sourceMask η s) (sourceMask_lt η s) i hi
  have hv:=selected_getD η (sourceNibble s 0) (sourceNibble s 1)
    (sourceNibble s 2) (sourceNibble s 3) hi
  have he : [sourceNibble s 0,sourceNibble s 1,sourceNibble s 2,sourceNibble s 3][ids[i]!]!
      =sourceNibble s (ids[i]!) := by
    generalize ids[i]! = j at *
    rcases (by omega : j=0∨j=1∨j=2∨j=3) with rfl|rfl|rfl|rfl <;> rfl
  change Spec.MlDsa.ofInt (VG.Proof.MlDsa.Sample.rbC η
    ([sourceNibble s 0,sourceNibble s 1,sourceNibble s 2,sourceNibble s 3][ids[i]!]!))=_ at hv
  rw [he] at hv
  exact hv

def extractCode : List Instr :=
 [.vop (.logic .and .v1 .v0 .v23),.vop (.shift .ushr .b16 .v0 .v0 4),
  .vop (.perm .zip1 .b16 .v0 .v1 .v0),.vop (.tbl .v1 .v0 .v25)]

def acceptCode : List Instr :=
 [.vop (.sub .s4 .v2 .v1 .v22),.vop (.shift .ushr .s4 .v2 .v2 31),
  .vop (.mul .v2 .v2 .v24)]

theorem source_accept {η : Nat} (hη : η=2∨η=4) (s : State) (e : Nat) :
    acceptWord η (nibbleWord (s.v .v0) e)=BitVec.ofNat 32
      (decide (sourceNibble s e<VG.Proof.MlDsa.Sample.rbB η)).toNat := by
  have hh:=acceptWord_decide hη (sourceNibble s e) (nibbleWord_bound _ _)
  simpa only [sourceNibble,BitVec.ofNat_toNat,BitVec.setWidth_eq] using hh

/-- The public rejection transcript determines the entire table index. -/
theorem nibbleMask_ok {η : Nat} (hη : η=2∨η=4) (s : State)
    (hm : s.v .v23=ofVBytes (fun _=>15)) (hi : s.v .v25=expandIndices)
    (hb : ∀e<4,vword (s.v .v22) e=BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η))
    (hw : ∀e<4,vword (s.v .v24) e=BitVec.ofNat 32 (2^e))
    (h15 : s.gpr .x11=15) :
    WP isa (.block (extractCode++acceptCode++maskCode)) s fun t=>
      Keep [.x6,.x7] s t ∧ t.mem=s.mem ∧ t.gpr .x6=BitVec.ofNat 64 (sourceMask η s) ∧
      (∀e<4,vword (t.v .v1) e=nibbleWord (s.v .v0) e) ∧
      (∀r,r∉[VReg.v0,.v1,.v2]→t.v r=s.v r) := by
  unfold extractCode
  refine extract_ok hm hi fun a ha hv => ?_
  refine acceptVector_ok η (fun e he=>by rw [ha.get .v22]; exact hb e he)
    (fun e he=>by rw [ha.get .v24]; exact hw e he) fun b hbb hbv => ?_
  have hc : VChg [.v0,.v1,.v2] s b := (ha.trans hbb).mono (by decide)
  have heq : b.v .v2=acceptanceVector
      (decide (sourceNibble s 0<VG.Proof.MlDsa.Sample.rbB η))
      (decide (sourceNibble s 1<VG.Proof.MlDsa.Sample.rbB η))
      (decide (sourceNibble s 2<VG.Proof.MlDsa.Sample.rbB η))
      (decide (sourceNibble s 3<VG.Proof.MlDsa.Sample.rbB η)) := by
    apply vector_eq_of_words
    intro e he
    rw [hbv e he,hv e he,source_accept hη,acceptanceVector_words _ _ _ _ e he]
    rcases (by omega : e=0∨e=1∨e=2∨e=3) with rfl|rfl|rfl|rfl <;> rfl
  exact WP.mono (maskCode_ok b (by rw [hc.gpr]; exact h15)) fun t ⟨⟨⟨hmask,hmem⟩,hk⟩,hvec⟩=>
    ⟨(hc.keep.trans hk).mono (by decide),hmem.trans hc.mem,
      by rw [hmask,heq,maskReduce_eq]; rfl,
      fun e he=>by rw [hvec,hbb.get .v1]; exact hv e he,
      fun r hr=>by rw [hvec,hc.v r hr]⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
