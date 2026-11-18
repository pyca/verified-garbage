module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRead
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStore
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourExtract
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGuard
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTable
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMath
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `MlDsa.AArch64.Optimized.BoundedFourLoad`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourMask`, which only this module used -/

section

/-! ## From `BoundedFourAccept.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- Each acceptance bit occupies a distinct bit in the scalar table index. -/
theorem acceptVector_ok (η : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hb : ∀e<4,vword (s.v .v22) e=BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η))
    (hw : ∀e<4,vword (s.v .v24) e=BitVec.ofNat 32 (2^e))
    (k : ∀t,VChg [.v2] s t →
      (∀e<4,vword (t.v .v2) e=acceptWord η (vword (s.v .v1) e)*BitVec.ofNat 32 (2^e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([.vop (.sub .s4 .v2 .v1 .v22),
      .vop (.shift .ushr .s4 .v2 .v2 31),.vop (.mul .v2 .v2 .v24)] : List Instr)++rest)) s Q := by
  refine wp_vop (d := .v2) rfl fun a ha => wp_vop (d := .v2) rfl fun b hbb =>
    wp_vop (d := .v2) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hbb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hbb.get .v24 (by decide),
      ha.get .v24 (by decide),hw e he,hbb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,hb e he]
    rfl

/-- Horizontal scalar reduction of the four weighted acceptance bits. -/
def maskReduce (x : BitVec 128) : BitVec 64 :=
  let a:=x.extractLsb' 0 64+x.extractLsb' 64 64
  (a+(a>>>32)) &&& 15

def acceptanceVector (a b c d : Bool) : BitVec 128 :=
  ofVWords (BitVec.ofNat 32 a.toNat) (BitVec.ofNat 32 (2*b.toNat))
    (BitVec.ofNat 32 (4*c.toNat)) (BitVec.ofNat 32 (8*d.toNat))

theorem maskReduce_eq (a b c d : Bool) :
    maskReduce (acceptanceVector a b c d)=BitVec.ofNat 64 (maskOf a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem acceptanceVector_words (a b c d : Bool) :
    ∀e<4,vword (acceptanceVector a b c d) e=
      BitVec.ofNat 32 (([a,b,c,d][e]!).toNat)*BitVec.ofNat 32 (2^e) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem vector_eq_of_words {x y : BitVec 128}
    (h : ∀e<4,vword x e=vword y e) : x=y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hh:=congrArg (fun b : BitVec 32=>b.getLsbD (k%32)) (h (k/32) (by omega_using [hk]))
  have hb : k%32<32:=Nat.mod_lt _ (by decide)
  have hd : 32*(k/32)+k%32=k:=by omega_using []
  simpa only [vword,BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and,hd] using hh

theorem acceptWord_decide {η : Nat} (hη : η=2∨η=4) : ∀b<16,
    acceptWord η (BitVec.ofNat 32 b)=
      BitVec.ofNat 32 (decide (b<VG.Proof.MlDsa.Sample.rbB η)).toNat := by
  rcases hη with rfl|rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMask.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def maskCode : List Instr :=
 [.umov .x .x6 .v2 0,.umov .x .x7 .v2 1,.add .x .x6 .x6 .x7,
  .lsr .x .x7 .x6 32,.add .x .x6 .x6 .x7,.logic .and .x .x6 .x6 .x11]

theorem exec_umov_double (s : State) (d : Reg) (n : VReg) {i : Nat} (hi : i<2) :
    exec (.umov .x d n i) s=some (s.write .x d ((s.v n).extractLsb' (i*64) 64)) := by
  simp only [exec,Size.bits,show i*64<128 by omega_using [hi],ite_true,Nat.mul_comm]

theorem maskCode_ok (s : State) (h15 : s.gpr .x11=15) :
    WP isa (.block maskCode) s fun t =>
      ((t.gpr .x6=maskReduce (s.v .v2) ∧ t.mem=s.mem) ∧ Keep [.x6,.x7] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskCode maskReduce
  arun [exec_umov_double (i := 0) (hi := by decide),
    exec_umov_double (i := 1) (hi := by decide),h15]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourExtractMachine.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BoundedFourSelect.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices)

def nibbleMask (η a b c d : Nat) : Nat :=
 maskOf (decide (a<rbB η)) (decide (b<rbB η)) (decide (c<rbB η)) (decide (d<rbB η))

theorem nibbleMask_lt (η a b c d : Nat) : nibbleMask η a b c d<16 := maskOf_lt _ _ _ _

/-- The table-selected prefix is precisely the old scalar rejection filter. -/
theorem selected_values (η a b c d : Nat) :
    ((acceptedIndices (nibbleMask η a b c d)).map
      (fun i=>ofInt (rbC η ([a,b,c,d][i]!))))=accepted η [a,b,c,d] := by
  unfold nibbleMask
  rw [maskOf_indices]
  simp only [accepted,List.filter_cons,List.filter_nil,List.map_append]
  by_cases ha : a<rbB η <;> by_cases hb : b<rbB η <;>
    by_cases hc : c<rbB η <;> by_cases hd : d<rbB η <;>
    simp [ha,hb,hc,hd]

theorem selected_count (η a b c d : Nat) :
    (acceptedIndices (nibbleMask η a b c d)).length=(accepted η [a,b,c,d]).length := by
  simpa only [List.length_map] using congrArg List.length (selected_values η a b c d)

theorem selected_getD (η a b c d : Nat) {i : Nat}
    (hi : i<(acceptedIndices (nibbleMask η a b c d)).length) :
    ofInt (rbC η ([a,b,c,d][(acceptedIndices (nibbleMask η a b c d))[i]!]!))=
      (accepted η [a,b,c,d]).getD i 0 := by
  rw [←selected_values η a b c d,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa only [List.length_map] using hi),Option.getD_some,
    List.getElem_map,getElem!_pos (acceptedIndices (nibbleMask η a b c d)) i hi]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

theorem vector_eq_of_bytes {x y : BitVec 128}
    (h : ∀i<16,vbyte x i=vbyte y i) : x=y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hh:=congrArg (fun b : BitVec 8=>b.getLsbD (k%8)) (h (k/8) (by omega_using [hk]))
  have h8 : k%8<8:=Nat.mod_lt _ (by decide)
  have hd : 8*(k/8)+k%8=k:=by omega_using []
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
    rcases (by omega_using [hn] : j=0∨j=1∨j=2∨j=3) with rfl|rfl|rfl|rfl <;> rfl
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
    rcases (by omega_using [he] : e=0∨e=1∨e=2∨e=3) with rfl|rfl|rfl|rfl <;> rfl
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
  have h32 : 8*i+k<32:=by omega_using [hi, hk]
  simp only [loadedVector,ofVWords,vbyte,BitVec.getLsbD_extractLsb',hk,decide_true,
    Bool.true_and,BitVec.getLsbD_append,h32,ite_true,Mem.readW,BitVec.getLsbD_setWidth]
  rw [getLsbD_read m 4 _ _ (by omega_using [hi, hk])]
  have hd : (8*i+k)/8=i:=by omega_using [hk]
  have hm : (8*i+k)%8=k:=by omega_using [hk]
  rw [hd,hm]

theorem loadedVector_nibbles (m : Mem) (p : Addr) :
    (List.range 4).map (fun e=>(nibbleWord (loadedVector m p) e).toNat)=
      nibbles (m p) (m (p+1)) := by
  have hw (e : Nat) (he:e<4) :
      (nibbleWord (loadedVector m p) e).toNat=
        if e%2=0 then (m (p+BitVec.ofNat 64 (e/2))).toNat%16
        else (m (p+BitVec.ofNat 64 (e/2))).toNat/16 := by
    rw [nibbleWord_value,loadedVector_byte _ _ (by omega_using [he]),BitVec.toNat_ofNat]
    have hb:=(m (p+BitVec.ofNat 64 (e/2))).isLt
    split <;> rw [Nat.mod_eq_of_lt (by omega_using [])]
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

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourAdvance`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def advanceCore : List Instr :=
 [.lsl .x .x7 .x6 2,.add .x .x3 .x3 .x7,.sub .x .x4 .x4 .x6,
  .addImm .x .x2 .x2 2,.subImm .x .x5 .x5 2]

private theorem countShift : ∀c≤4,(BitVec.ofNat 64 c<<<2)=BitVec.ofNat 64 (4*c) := by decide

theorem advanceCore_ok {s : State} {c r n : Nat} (hc : c≤4) (hr : c≤r) (hn : 2≤n)
    (h6 : s.gpr .x6=BitVec.ofNat 64 c)
    (h4 : s.gpr .x4=BitVec.ofNat 64 r) (h5 : s.gpr .x5=BitVec.ofNat 64 n) :
    WP isa (.block advanceCore) s fun t=>
      ((t.gpr .x2=s.gpr .x2+2 ∧ t.gpr .x3=s.gpr .x3+BitVec.ofNat 64 (4*c) ∧
        t.gpr .x4=BitVec.ofNat 64 (r-c) ∧ t.gpr .x5=BitVec.ofNat 64 (n-2) ∧ t.mem=s.mem) ∧
        Keep [.x2,.x3,.x4,.x5,.x7] s t) ∧ t.v=s.v := by
  apply WP.keepV (by decide)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advanceCore
  arun [h6,h4,h5,countShift c hc]
  exact ⟨rfl,BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega_using [hc]) hr,
    BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) hn⟩

theorem guard_ok {s : State} (h16 : s.gpr .x16=4) (h0 : s.gpr .x0=0) :
    WP isa (.block [.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs]) s fun t=>
      Only [.x8] s t ∧ t.v=s.v ∧
      t.gpr .x8=if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0 := by
  refine WP.mono (ResidentRej.compareChooseReg_ok .x8 .x4 .x16 .x5 .x0
    (by decide) (by decide)) fun t ⟨hk,hv,hx⟩=>⟨hk,hv,?_⟩
  rw [h16,h0] at hx
  exact hx

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourState`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def constantRegs : List Reg := [.x0,.x9,.x10,.x11,.x12,.x15,.x16]
def constantVecs : List VReg := [.v18,.v19,.v20,.v21,.v22,.v23,.v24,.v25]
def bodyRegs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x13]
def bodyVecs : List VReg := [.v0,.v1,.v2,.v6]

structure Consts (η : Nat) (table : Addr) (s : State) : Prop where
 zero : s.gpr .x0=0
 mask : s.gpr .x11=15
 table : s.gpr .x12=table
 four : s.gpr .x16=4
 thirteen : ∀e<4,vword (s.v .v18) e=13#32
 five : ∀e<4,vword (s.v .v19) e=5#32
 etaQ : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η)
 q : ∀e<4,vword (s.v .v21) e=8380417#32
 bound : ∀e<4,vword (s.v .v22) e=BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η)
 nibble : s.v .v23=ofVBytes (fun _=>15)
 weights : ∀e<4,vword (s.v .v24) e=BitVec.ofNat 32 (2^e)
 expand : s.v .v25=expandIndices
 scalarQ : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q
 scalarEta : s.gpr .x10=BitVec.ofNat 64 η
 scalarBound : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)

theorem Consts.keep {η : Nat} {table : Addr} {s t : State} (h : Consts η table s)
    {rs : List Reg} (hk : Keep rs s t)
    (hg : ∀r∈constantRegs,r∉rs)
    (hv : ∀r∈constantVecs,t.v r=s.v r) : Consts η table t := by
  constructor
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.zero
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.mask
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.table
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.four
  · rw [hv _ (by decide)]; exact h.thirteen
  · rw [hv _ (by decide)]; exact h.five
  · rw [hv _ (by decide)]; exact h.etaQ
  · rw [hv _ (by decide)]; exact h.q
  · rw [hv _ (by decide)]; exact h.bound
  · rw [hv _ (by decide)]; exact h.nibble
  · rw [hv _ (by decide)]; exact h.weights
  · rw [hv _ (by decide)]; exact h.expand
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.scalarQ
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.scalarEta
  · rw [hk.gpr _ (hg _ (by decide))]; exact h.scalarBound

theorem Consts.body {η : Nat} {table : Addr} {s t : State} (h : Consts η table s)
    (hk : Keep bodyRegs s t) (hv : ∀r,r∉bodyVecs→t.v r=s.v r) : Consts η table t :=
  h.keep hk (by decide) (fun r hr=>hv r (by
    simp only [constantVecs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ## From `BoundedFourSelectMachine.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorVal acceptedIndices)

/-- The vector parser through reduction and table compaction, before its store. -/
def selectCode (η : Nat) : List Instr :=
 (extractCode++acceptCode++maskCode)++
 (([.lsl .x .x6 .x6 6,.add .x .x13 .x12 .x6] : List Instr)++
 (([.ldrq .v6 .x13 0,.ldr .x .x6 .x13 32] : List Instr)++
 (vectorVal η++[.vop (.tbl .v1 .v1 .v6)])))

theorem selectCode_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr}
    (hC : Consts η p s) (hT : TableAt s.mem p)
    (hR : ∀m<16,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (64*m)) 16 ∧
      InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (64*m)+32) 8) :
    WP isa (.block (selectCode η)) s fun t=>
      Keep [.x6,.x7,.x13] s t ∧ t.mem=s.mem ∧
      t.gpr .x6=BitVec.ofNat 64 (sourceValues η s).length ∧
      (∀i<(sourceValues η s).length,vword (t.v .v1) i=
        VG.Proof.MlDsa.Sample.zw ((sourceValues η s).getD i 0)) ∧
      (∀r,r∉bodyVecs→t.v r=s.v r) := by
  unfold selectCode
  rw [WP.block_append_iff]
  refine WP.mono (nibbleMask_ok hη s hC.nibble hC.expand hC.bound hC.weights hC.mask)
    fun a ⟨hak,ham,hamask,han,hav⟩=>?_
  rw [WP.block_append_iff]
  have hma:=sourceMask_lt η s
  refine WP.mono (tableAddress_ok (s := a) (p := p) (mask := sourceMask η s) hma (by rw [hak.gpr .x12 (by decide)]; exact hC.table) hamask)
    fun b ⟨⟨⟨hbaddr,hbm⟩,hbk⟩,hbv⟩=>?_
  rw [WP.block_append_iff]
  have hbk' : Keep [.x6,.x7,.x13] s b:=(hak.trans hbk).mono (by decide)
  have hbmem : b.mem=s.mem:=hbm.trans ham
  refine WP.mono (tableRead_ok (s := b) (p := p) (mask := sourceMask η s) hma (by rw [hbmem]; exact hT) hbaddr
    (by rw [hbk'.rd,hbk'.wr,hbaddr]; exact (hR _ hma).1)
    (by rw [hbk'.rd,hbk'.wr,hbaddr]; exact (hR _ hma).2))
    fun c ⟨hck,hcm,hc6,hcount,hcv⟩=>?_
  have hck' : Keep [.x6,.x7,.x13] s c:=(hbk'.trans hck).mono (by decide)
  have hcmem : c.mem=s.mem:=hcm.trans hbmem
  have hvc (r : VReg) (hr : r∉bodyVecs) : c.v r=s.v r := by
    rw [hcv r (by intro he; subst r; exact hr (by decide)),hbv]
    exact hav r (by
      intro he
      apply hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl <;> decide)
  have hcn (e : Nat) (he:e<4) : vword (c.v .v1) e=nibbleWord (s.v .v0) e := by
    rw [hcv .v1 (by decide),hbv]; exact han e he
  refine valueCompact_ok hη hma
    (fun e he=>by rw [hvc .v18 (by decide)]; exact hC.thirteen e he)
    (fun e he=>by rw [hvc .v19 (by decide)]; exact hC.five e he)
    (fun e he=>by rw [hvc .v21 (by decide)]; exact hC.q e he)
    (fun e he=>by rw [hvc .v20 (by decide)]; exact hC.etaQ e he) hc6
    (fun e he=>by rw [hcn e he]; exact nibbleWord_bound _ _) fun t ht hv=>?_
  apply VG.Proof.MlKem.AArch64.wp_nil
  refine ⟨(hck'.trans ht.keep).mono (by decide),ht.mem.trans hcmem,?_,?_,?_⟩
  · rw [ht.gpr,hcount,sourceMask_count]
  · intro i hi
    have hii : i<(acceptedIndices (sourceMask η s)).length:=by rwa [sourceMask_count]
    rw [hv i hii,hcn _ (index_bound _ hma i hii)]
    change BitVec.ofNat 32 (Spec.MlDsa.ofInt (VG.Proof.MlDsa.Sample.rbC η
      (sourceNibble s ((acceptedIndices (sourceMask η s))[i]!)))).val=_
    rw [sourceValues_lane η s hii]
  · intro r hr
    rw [ht.v r (by
      intro he
      apply hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl <;> decide)]
    exact hvc r hr

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

def bodyValues (η : Nat) (s : State) : List Zq :=
 accepted η (nibbles (s.mem (s.gpr .x2)) (s.mem (s.gpr .x2+1)))

theorem sourceValues_loaded {η : Nat} {s a : State}
    (hv : a.v .v0=loadedVector s.mem (s.gpr .x2)) : sourceValues η a=bodyValues η s := by
  unfold sourceValues bodyValues sourceNibble
  rw [hv]
  have h:=loadedVector_nibbles s.mem (s.gpr .x2)
  simp only [List.range,List.range.loop,List.map_cons,List.map_nil] at h
  rw [h]

theorem vectorBody_eq (η : Nat) : vectorBody true η=
    ([.ldr .w .x6 .x2 0,.vop (.dup .s4 .v0 .x6)] : List Instr)++
    (selectCode η++(([.strq .v1 .x3 0] : List Instr)++
    (advanceCore++([.subs .x .x8 .x4 .x16,.cselc .x .x8 .x5 .x0 .hs] : List Instr)))) := by
  simp only [vectorBody,selectCode,extractCode,acceptCode,maskCode,advanceCore,
    ite_true,List.append_assoc,List.cons_append,List.nil_append]

structure BodyPost (η : Nat) (s t : State) (p : Addr) (L : List Zq) (bytes : Nat) : Prop where
 keep : Keep bodyRegs s t
 frame : Frame [polyR p] s.mem t.mem
 vectors : ∀r,r∉bodyVecs→t.v r=s.v r
 stored : Stored t.mem p (L++bodyValues η s)
 input : t.gpr .x2=s.gpr .x2+2
 output : t.gpr .x3=coeffAddr p (L++bodyValues η s).length
 remaining : t.gpr .x4=BitVec.ofNat 64 (256-(L++bodyValues η s).length)
 remainingBytes : t.gpr .x5=BitVec.ofNat 64 (bytes-2)
 guard : t.gpr .x8=if (L++bodyValues η s).length≤252 then BitVec.ofNat 64 (bytes-2) else 0

theorem vectorBody_ok {η : Nat} (hη : η=2∨η=4) {s : State} {table p : Addr}
    {L : List Zq} {bytes : Nat} (hC : Consts η table s) (hT : TableAt s.mem table)
    (hR : ∀m<16,InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 (64*m)) 16 ∧
      InRegions (s.rd++s.wr) (table+BitVec.ofNat 64 (64*m)+32) 8)
    (hi : InRegions (s.rd++s.wr) (s.gpr .x2) 4)
    (hL : L.length≤252) (hN : 2≤bytes) (hS : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : s.gpr .x4=BitVec.ofNat 64 (256-L.length))
    (h5 : s.gpr .x5=BitVec.ofNat 64 bytes)
    (hW : InRegions s.wr (coeffAddr p L.length) 16) :
    WP isa (.block (vectorBody true η)) s fun t=>BodyPost η s t p L bytes := by
  rw [vectorBody_eq,WP.block_append_iff]
  refine WP.mono (loadDup_ok s hi) fun a ⟨hak,ham,hav0,hav⟩=>?_
  have hCa : Consts η table a:=hC.keep hak (by decide) (fun r hr=>hav r (by
    simp only [constantVecs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))
  rw [WP.block_append_iff]
  refine WP.mono (selectCode_ok hη hCa (by rw [ham]; exact hT)
    (fun m hm=>by rw [hak.rd,hak.wr]; exact hR m hm)) fun b ⟨hbk,hbm,hcount,hvals,hbv⟩=>?_
  have hAB : sourceValues η a=bodyValues η s:=sourceValues_loaded hav0
  rw [hAB] at hcount hvals
  have hA : (bodyValues η s).length≤4:=by rw [←hAB]; exact sourceValues_length _ _
  have hbk' : Keep [.x6,.x7,.x13] s b:=(hak.trans hbk).mono (by decide)
  have hbmem : b.mem=s.mem:=hbm.trans ham
  have hbvec (r : VReg) (hr : r∉bodyVecs) : b.v r=s.v r := by
    rw [hbv r hr,hav r (by intro he; subst r; exact hr (by decide))]
  rw [WP.block_append_iff]
  refine WP.mono (storeAccepted_ok (s := b) (p := p) (L := L) (A := bodyValues η s) (by omega_using [hL]) hA (by rw [hbmem]; exact hS)
    (by rw [hbk'.gpr .x3 (by decide)]; exact h3)
    (by rw [hbk'.wr]; exact hW) hvals) fun c ⟨hck,hcg,hcv,hcf,hcs⟩=>?_
  have hck' : Keep [.x6,.x7,.x13] s c:=(hbk'.trans hck).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (advanceCore_ok (s := c) (c := (bodyValues η s).length) (r := 256-L.length) (n := bytes) hA (by omega_using [hL, hA]) hN
    (by rw [hcg]; exact hcount)
    (by rw [hck'.gpr .x4 (by decide)]; exact h4)
    (by rw [hck'.gpr .x5 (by decide)]; exact h5))
    fun d ⟨⟨⟨hd2,hd3,hd4,hd5,hdmem⟩,hdk⟩,hdvec⟩=>?_
  have hdk' : Keep bodyRegs s d:=(hck'.trans hdk).mono (by decide)
  refine WP.mono (guard_ok
    (by rw [hdk'.gpr .x16 (by decide)]; exact hC.four)
    (by rw [hdk'.gpr .x0 (by decide)]; exact hC.zero)) fun t ⟨htk,htv,ht8⟩=>?_
  refine ⟨(hdk'.trans htk.keep).mono (by decide),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htk.mem,hdmem,←hbmem]; exact hcf
  · intro r hr
    rw [htv,hdvec,hcv,hbvec r hr]
  · rw [htk.mem,hdmem]; exact hcs
  · rw [htk.get .x2,hd2,hck'.gpr .x2 (by decide)]
  · rw [htk.get .x3,hd3,hck'.gpr .x3 (by decide),h3,List.length_append]
    exact VG.Proof.MlDsa.Arith.coeffAddr_add p L.length (bodyValues η s).length
  · rw [htk.get .x4,hd4,List.length_append]
    congr 1; omega_using []
  · rw [htk.get .x5,hd5]
  · rw [ht8,hd4,hd5,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using []),List.length_append]
    by_cases he : L.length+(bodyValues η s).length≤252
    · rw [ite_eq_left (by omega_using [he]),ite_eq_left he]
    · rw [ite_eq_right (by omega_using [he]),ite_eq_right he]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
