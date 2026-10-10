import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourExtract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSelect

/-! ## From `BoundedFourExtractMachine.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

theorem vector_eq_of_bytes {x y : BitVec 128}
    (h : ∀i<16,vbyte x i=vbyte y i) : x=y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hh:=congrArg (fun b : BitVec 8=>b.getLsbD (k%8)) (h (k/8) (by omega))
  have h8 : k%8<8:=Nat.mod_lt _ (by decide)
  have hd : 8*(k/8)+k%8=k:=by omega
  simpa only [vbyte,BitVec.getLsbD_extractLsb',h8,decide_true,Bool.true_and,hd] using hh

theorem and_byteMask (x : BitVec 128) (m : BitVec 8) :
    x &&& (ofVBytes fun _=>m)=ofVBytes (fun i=>vbyte x i &&& m) := by
  apply vector_eq_of_bytes
  intro i hi
  rw [vbyte_ofVBytes _ hi]
  change (x &&& (ofVBytes fun _=>m)).extractLsb' (8*i) 8=_
  rw [BitVec.extractLsb'_and]
  exact congrArg (fun z=>vbyte x i &&& z) (vbyte_ofVBytes _ hi)

/-- Four low-to-high half-bytes are widened without observing later stream bytes. -/
theorem extract_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hm : s.v .v23=ofVBytes (fun _=>15)) (hi : s.v .v25=expandIndices)
    (k : ∀t,VChg [.v0,.v1] s t →
      (∀e<4,vword (t.v .v1) e=nibbleWord (s.v .v0) e) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([.vop (.logic .and .v1 .v0 .v23),
      .vop (.shift .ushr .b16 .v0 .v0 4),.vop (.perm .zip1 .b16 .v0 .v1 .v0),
      .vop (.tbl .v1 .v0 .v25)] : List Instr)++rest)) s Q := by
  refine wp_vop (d := .v1) rfl fun a ha => wp_vop (d := .v0) rfl fun b hb =>
    wp_vop (d := .v0) rfl fun c hc => wp_vop (d := .v1) rfl fun t ht => ?_
  refine k t ((((ha.chg.trans hb.chg).trans hc.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,hc.get .v25 (by decide),hb.get .v25 (by decide),ha.get .v25 (by decide),hi,
      hc.v,hb.get .v1 (by decide),ha.v,hm,and_byteMask,hb.v,ha.get .v0 (by decide)]
    exact extractVector_word _ he

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourPrefix.lean` -/

section

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

end

/-! ## From `BoundedFourLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def loadedVector (m : Mem) (p : Addr) : BitVec 128 :=
 let w:=m.readW p 32
 ofVWords w w w w

theorem loadedVector_byte (m : Mem) (p : Addr) {i : Nat} (hi : i<4) :
    vbyte (loadedVector m p) i=m (p+BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h32 : 8*i+k<32:=by omega
  simp only [loadedVector,ofVWords,vbyte,BitVec.getLsbD_extractLsb',hk,decide_true,
    Bool.true_and,BitVec.getLsbD_append,h32,ite_true,Mem.readW,BitVec.getLsbD_setWidth]
  rw [getLsbD_read m 4 _ _ (by omega)]
  have hd : (8*i+k)/8=i:=by omega
  have hm : (8*i+k)%8=k:=by omega
  rw [hd,hm]

theorem loadedVector_nibbles (m : Mem) (p : Addr) :
    (List.range 4).map (fun e=>(nibbleWord (loadedVector m p) e).toNat)=
      nibbles (m p) (m (p+1)) := by
  have hw (e : Nat) (he:e<4) :
      (nibbleWord (loadedVector m p) e).toNat=
        if e%2=0 then (m (p+BitVec.ofNat 64 (e/2))).toNat%16
        else (m (p+BitVec.ofNat 64 (e/2))).toNat/16 := by
    rw [nibbleWord_value,loadedVector_byte _ _ (by omega),BitVec.toNat_ofNat]
    have hb:=(m (p+BitVec.ofNat 64 (e/2))).isLt
    split <;> rw [Nat.mod_eq_of_lt (by omega)]
  simp only [List.range,List.range.loop,List.map_cons,List.map_nil]
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [nibbles,Nat.reduceMod,Nat.reduceDiv,Nat.reduceEqDiff,ite_true,ite_false,
    BitVec.ofNat_eq_ofNat,BitVec.add_zero]

theorem loadDup_ok (s : State) (hin : InRegions (s.rd++s.wr) (s.gpr .x2) 4) :
    WP isa (.block [.ldr .w .x6 .x2 0,.vop (.dup .s4 .v0 .x6)]) s fun t=>
      Keep [.x6] s t ∧ t.mem=s.mem ∧ t.v .v0=loadedVector s.mem (s.gpr .x2) ∧
      (∀r,r≠.v0→t.v r=s.v r) := by
  have hh : WP isa (.block [.ldr .w .x6 .x2 0]) s fun a=>
      (Only [.x6] s a ∧ a.gpr .x6=(s.mem.readW (s.gpr .x2) 32).setWidth 64) ∧ a.v=s.v :=
    WP.keepV (by decide) (wp_ldrw (by decide) (by simp) hin fun a ha hv=>wp_nil ⟨ha,hv⟩)
  change WP isa (.block (([.ldr .w .x6 .x2 0] : List Instr)++[.vop (.dup .s4 .v0 .x6)])) s _
  rw [WP.block_append_iff]
  refine WP.mono hh fun a ⟨⟨ha,hv⟩,hav⟩=>?_
  refine wp_vop (d := .v0) rfl fun t ht=>wp_nil ?_
  refine ⟨(ha.keep.trans ht.chg.keep).mono (by decide),ht.mem.trans ha.mem,?_,?_⟩
  · rw [ht.v,hv]
    simp only [BitVec.setWidth_setWidth_of_le _ (show 32≤64 by decide),BitVec.setWidth_eq]
    rfl
  · intro r hr
    rw [ht.other r hr,hav]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
