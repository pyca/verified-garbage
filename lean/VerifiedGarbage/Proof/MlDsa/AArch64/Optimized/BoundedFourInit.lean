module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitWord
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRead
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourStore
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejGuard
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTable
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCompact
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedLoop

/-! ### `MlDsa.AArch64.Optimized.BoundedFourScalarPair`, which this module and modules that import it used -/

section

/-! ## From `BoundedFourScalarLoad.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Sample (rbLoad)

private theorem lowByte : ∀b : Byte,(b.setWidth 64 &&& 15)=BitVec.ofNat 64 (b.toNat%16) := by decide
private theorem highByte : ∀b : Byte,(b.setWidth 64 >>>4)=BitVec.ofNat 64 (b.toNat/16) := by decide

theorem scalarLoad_ok {s : State} (h11 : s.gpr .x11=15)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2) 1) :
    WP isa (.block rbLoad) s fun t=>Only [.x2,.x5,.x6,.x7] s t ∧
      t.gpr .x2=s.gpr .x2+1 ∧ t.gpr .x5=s.gpr .x5-1 ∧
      t.gpr .x6=(s.mem (s.gpr .x2)).setWidth 64 ∧
      t.gpr .x7=BitVec.ofNat 64 ((s.mem (s.gpr .x2)).toNat%16) := by
  unfold rbLoad
  refine wp_ldrb (by decide) (by simp) hr fun a ha h6=>
    wp_addImm (by decide) fun b hb h2=>wp_subImm (by decide) fun c hc h5=>
    wp_and fun t ht h7=>wp_nil ?_
  refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_,?_,?_,?_⟩
  · rw [ht.get .x2,hc.get .x2,h2,ha.get .x2]
    rfl
  · rw [ht.get .x5,h5,hb.get .x5,ha.get .x5]
    rfl
  · rw [ht.get .x6,hc.get .x6,hb.get .x6,h6]
  · rw [h7,hc.get .x6,hb.get .x6,h6,hc.get .x11,hb.get .x11,ha.get .x11,h11]
    exact lowByte _

theorem scalarHigh_ok {s : State} {b : Byte} (h6 : s.gpr .x6=b.setWidth 64) :
    WP isa (.block [.lsr .x .x7 .x6 4]) s fun t=>Only [.x7] s t ∧
      t.gpr .x7=BitVec.ofNat 64 (b.toNat/16) := by
  refine wp_lsr (by decide) fun t ht h7=>wp_nil ⟨ht,?_⟩
  rw [h7,h6]
  exact highByte b

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourScalarPair.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Sample (rbTry)

abbrev ScalarConsts := VG.Proof.MlDsa.AArch64.Sample.RejBounded.Consts

def scalarPairRegs : List Reg := [.x3,.x4,.x7,.x8,.x12,.x13,.x14]
def scalarPair (η : Nat) : Prog isa :=
 .ite (.zero .x .x4) (.block [])
   (.seq (.block (rbTry η++[.lsr .x .x7 .x6 4]))
     (.ite (.zero .x .x4) (.block []) (.block (rbTry η))))

theorem remaining_zero {s : State} {L : List Zq}
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length≤256) :
    isa.eval (.zero .x .x4) s=some (decide (L.length=256)) := by
  rw [eval_zero,eq_zero_iff,h4]
  congr 1
  exact decide_eq_decide.mpr (by omega_arith)

structure ScalarPairPost (η : Nat) (s t : State) (p : Addr) (L : List Zq) (b : Byte) : Prop where
 keep : Keep scalarPairRegs s t
 frame : Frame [polyR p] s.mem t.mem
 output : t.gpr .x3=coeffAddr p (rbStep η L b).length
 remaining : (t.gpr .x4).toNat=256-(rbStep η L b).length
 stored : Stored t.mem p (rbStep η L b)

theorem scalarPair_ok {η : Nat} (hη : η=2∨η=4) {s : State} {p : Addr} {L : List Zq} {b : Byte}
    (hC : ScalarConsts η s) (hL : L.length≤256) (hS : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (h6 : s.gpr .x6=b.setWidth 64) (h7 : s.gpr .x7=BitVec.ofNat 64 (b.toNat%16))
    (hW : ∀j<256,InRegions s.wr (coeffAddr p j) 4) :
    WP isa (scalarPair η) s fun t=>ScalarPairPost η s t p L b := by
  unfold scalarPair
  by_cases hfull : L.length=256
  · have he : rbStep η L b=L:=by simp only [rbStep,n,hfull,Nat.lt_irrefl,ite_false]
    refine WP.ite true (by rw [remaining_zero h4 hL,decide_eq_true hfull])
      (fun _=>WP.block_nil_iff.mpr ?_) (fun h=>nomatch h)
    exact ⟨Keep.refl _ _,Frame.refl _ _,by rwa [he],by rwa [he],by rwa [he]⟩
  · refine WP.ite false (by rw [remaining_zero h4 hL,decide_eq_false hfull]) (fun h=>nomatch h) fun _=>?_
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok hη
      (by omega_arith) hC h7 h3 h4 (by omega_arith) hS (hW _ (by omega_arith)))
      fun a ⟨hak,haf,ha3,ha4,has⟩=>?_
    refine WP.mono (scalarHigh_ok (s := a) (b := b) (by rw [hak.gpr .x6 (by decide)]; exact h6))
      fun c ⟨hck,hc7⟩=>?_
    let L1:=hbTry η L (b.toNat%16)
    have hL1 : L1.length≤256:=by
      have hh:=hbTry_length η L (b.toNat%16)
      have hb:=halfByteOk_le η (b.toNat%16)
      dsimp only [L1]; omega_arith
    have hc4 : (c.gpr .x4).toNat=256-L1.length:=by rw [hck.get .x4]; exact ha4
    have hcs : Stored c.mem p L1:=by rw [hck.mem]; exact has
    have hcf : Frame [polyR p] s.mem c.mem:=by rw [hck.mem]; exact haf
    have hkeep : Keep scalarPairRegs s c:=(hak.trans hck.keep).mono (by decide)
    by_cases hfull1 : L1.length=256
    · have he : rbStep η L b=L1:=by
        simp only [rbStep,n,ifT (by omega_arith : L.length<256)]
        rw [ifF (by change ¬L1.length<256; omega_arith)]
      refine WP.ite true (by rw [remaining_zero hc4 hL1,decide_eq_true hfull1])
        (fun _=>WP.block_nil_iff.mpr ?_) (fun h=>nomatch h)
      exact ⟨hkeep,hcf,by rw [he,hck.get .x3]; exact ha3,by rwa [he],by rwa [he]⟩
    · have he : rbStep η L b=hbTry η L1 (b.toNat/16):=by
        simp only [rbStep,n,ifT (by omega_arith : L.length<256)]
        rw [ifT (by change L1.length<256; omega_arith)]
      refine WP.ite false (by rw [remaining_zero hc4 hL1,decide_eq_false hfull1]) (fun h=>nomatch h) fun _=>?_
      refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejBounded.try_ok hη
        (by have:=b.isLt; omega_arith) (hC.keep hkeep (by decide)) hc7
        (by rw [hck.get .x3]; exact ha3) hc4 (by omega_arith) hcs
        (by rw [hkeep.wr]; exact hW _ (by omega_arith))) fun t ⟨htk,htf,ht3,ht4,hts⟩=>?_
      exact ⟨(hkeep.trans htk).mono (by decide),hcf.trans htf,by rwa [he],by rwa [he],by rwa [he]⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourBody`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourMath`, which this module and modules that import it used -/

section

/-! The bounded sampler's vector groups preserve the standard nibble order.
Only the accepted prefix is meaningful while the parser is running; a failed
whole polynomial is cleared by the final mask. -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices)

/-- The four low-to-high half-bytes consumed by one vector iteration. -/
def nibbles (a b : Byte) : List Nat :=
 [a.toNat % 16, a.toNat / 16, b.toNat % 16, b.toNat / 16]

/-- Values accepted by a bounded sampler from a list of half-bytes. -/
def accepted (η : Nat) (bs : List Nat) : List Zq :=
 (bs.filter (fun b => b < rbB η)).map (fun b => ofInt (rbC η b))

theorem fold_hbTry (η : Nat) (hη : η=2 ∨ η=4) (a : List Zq) (bs : List Nat) :
    bs.foldl (hbTry η) a = a ++ accepted η bs := by
  induction bs generalizing a with
  | nil => simp [accepted]
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, hbTry_eq hη]
    by_cases h : b < rbB η
    · simp [accepted, h, List.append_assoc]
    · simp [accepted, h]

theorem rbStep_two {η : Nat} {a : List Zq} (ha : a.length≤254) (b : Byte) :
    rbStep η a b = hbTry η (hbTry η a (b.toNat%16)) (b.toNat/16) := by
  have h1 := halfByteOk_le η (b.toNat%16)
  simp only [rbStep, n]
  rw [ifT (by omega_using [ha]), ifT (by rw [hbTry_length]; omega_using [ha, h1])]

theorem twoBytes_values {η : Nat} (hη : η=2 ∨ η=4) {a : List Zq}
    (ha : a.length≤252) (b c : Byte) :
    rbFold η a [b,c] = a ++ accepted η (nibbles b c) := by
  have h1 := halfByteOk_le η (b.toNat%16)
  have h2 := halfByteOk_le η (b.toNat/16)
  have hlen : (hbTry η (hbTry η a (b.toNat%16)) (b.toNat/16)).length≤254 := by
    simp only [hbTry_length]; omega_using [ha, h1, h2]
  rw [rbFold, rbStep_two (by omega_using [ha]), rbFold, rbStep_two hlen]
  simpa only [nibbles, List.foldl_cons, List.foldl_nil, rbFold] using
    fold_hbTry η hη a (nibbles b c)

theorem accepted_length (η : Nat) (bs : List Nat) : (accepted η bs).length≤bs.length := by
  simpa only [accepted, List.length_map] using List.length_filter_le (fun b => b < rbB η) bs

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourExtract`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

def nibbleWord (x : BitVec 128) (i : Nat) : BitVec 32 :=
 ((if i%2=0 then vbyte x (i/2) &&& 15 else vbyte x (i/2) >>> 4) : BitVec 8).setWidth 32

def expandIndices : BitVec 128 := 0xffffff03ffffff02ffffff01ffffff00

private theorem narrowByte (b : BitVec 8) : (b.setWidth 128).setWidth 8=b := by
 rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]

theorem zip1_byte (x y : BitVec 128) {i : Nat} (hi : i<16) :
    vbyte (VPermOp.eval .zip1 .b16 x y) i=
      if i%2=0 then vbyte x (i/2) else vbyte y (i/2) := by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_map,List.length_range,
    vbyte_ofVBytes _ hi,Nat.reduceDiv]
  simp only [List.range,List.range.loop,List.map_cons,List.map_nil,List.flatMap_cons,
    List.flatMap_nil,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ]
  rcases (by omega_using [hi] : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7∨i=8∨i=9∨i=10∨i=11∨i=12∨i=13∨i=14∨i=15) with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [List.getD_cons_zero,List.getD_cons_succ,
      Nat.reduceDiv,Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,narrowByte]

def extractVector (x : BitVec 128) : BitVec 128 :=
 tableBytes (VPermOp.eval .zip1 .b16
   (ofVBytes fun i => vbyte x i &&& 15)
   (ofVBytes fun i => vbyte x i >>> 4)) expandIndices

theorem expandIndices_byte : ∀i<4,∀j<4,
    vbyte expandIndices (4*i+j)=if j=0 then BitVec.ofNat 8 i else 255 := by decide

theorem extractVector_byte (x : BitVec 128) {i j : Nat} (hi : i<4) (hj : j<4) :
    vbyte (extractVector x) (4*i+j)=
      if j=0 then (nibbleWord x i).setWidth 8 else 0 := by
  rw [extractVector,tableBytes,vbyte_ofVBytes _ (by omega_using [hi, hj]),expandIndices_byte i hi j hj]
  by_cases hz : j=0
  · subst j
    simp only [ite_true,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show i<256 by omega_using [hi])]
    rw [ite_eq_left (by omega_using [hi]),zip1_byte _ _ (by omega_using [hi]),
      vbyte_ofVBytes _ (by omega_using [hi]),vbyte_ofVBytes _ (by omega_using [hi])]
    simp only [nibbleWord]
    split <;> rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]
  · simp only [hz,ite_false]
    rw [ite_eq_right (by decide)]

private theorem widened_byte (b : BitVec 8) {j : Nat} (hj : j<4) :
    vbyte ((b.setWidth 32).setWidth 128) j=if j=0 then b else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vbyte,BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and,
    BitVec.getLsbD_setWidth]
  by_cases hz : j=0
  · subst j
    simp only [Nat.mul_zero,Nat.zero_add,show k<32 by omega_using [hk],show k<128 by omega_using [hk],decide_true,
      Bool.true_and,ite_true]
  · have h8 : ¬8*j+k<8 := by omega_using [hz]
    rw [BitVec.getLsbD_of_ge b _ (by omega_using [hz])]
    simp only [Bool.and_false,hz,ite_false]
    change false=(0#8).getLsbD k
    exact (BitVec.getLsbD_zero).symm

theorem extractVector_word (x : BitVec 128) {i : Nat} (hi : i<4) :
    vword (extractVector x) i=nibbleWord x i := by
  have hh := word_eq_of_bytes (extractVector x) ((nibbleWord x i).setWidth 128) i 0 (by
    intro j hj
    rw [extractVector_byte x hi hj]
    simp only [Nat.mul_zero,Nat.zero_add,nibbleWord]
    rw [widened_byte _ hj]
    rw [BitVec.setWidth_setWidth_of_le _ (show 8≤32 by decide),BitVec.setWidth_eq])
  simpa only [vword,Nat.mul_zero,BitVec.extractLsb'_setWidth_of_le (show 0+32≤128 by decide),
    BitVec.extractLsb'_eq_self] using hh

private theorem lowNibble_eq : ∀ b : BitVec 8,
    (b &&& 15).setWidth 32=BitVec.ofNat 32 (b.toNat%16) := by decide

private theorem highNibble_eq : ∀ b : BitVec 8,
    (b>>>4).setWidth 32=BitVec.ofNat 32 (b.toNat/16) := by decide

theorem nibbleWord_value (x : BitVec 128) (i : Nat) :
    nibbleWord x i=BitVec.ofNat 32
      (if i%2=0 then (vbyte x (i/2)).toNat%16 else (vbyte x (i/2)).toNat/16) := by
  unfold nibbleWord
  split
  · exact lowNibble_eq _
  · exact highNibble_eq _

theorem nibbleWord_bound (x : BitVec 128) (i : Nat) : (nibbleWord x i).toNat<16 := by
  rw [nibbleWord_value,BitVec.toNat_ofNat]
  have hb := (vbyte x (i/2)).isLt
  split <;> omega_using []

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

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

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourTraversal`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample

/-- Meaningful output after a prefix of a sampler stream. -/
def parsed (η : Nat) (L : List Zq) (X : List Byte) (done : Nat) : List Zq :=
 rbFold η L (X.take done)

theorem parsed_bound {η : Nat} {L : List Zq} {X : List Byte} (hL : L.length≤256) (done : Nat) :
    (parsed η L X done).length≤256 := rbFold_length_le hL _

theorem take_two {X : List Byte} {done : Nat} (h : done+2≤X.length) :
    X.take (done+2)=X.take done++[X[done]!,X[done+1]!] := by
  rw [show done+2=(done+1)+1 by omega_using [],List.take_succ_eq_append_getElem (by omega_using [h]),
    List.take_succ_eq_append_getElem (by omega_using [h]),List.append_assoc]
  simp only [getElem!_pos X done (by omega_using [h]),getElem!_pos X (done+1) (by omega_using [h])]
  rfl

theorem parsed_two {η : Nat} (hη : η=2∨η=4) {L : List Zq} {X : List Byte} {done : Nat}
    (hd : done+2≤X.length) (hL : (parsed η L X done).length≤252) :
    parsed η L X (done+2)=parsed η L X done++accepted η (nibbles X[done]! X[done+1]!) := by
  rw [parsed,take_two hd,rbFold_append]
  exact twoBytes_values hη hL _ _

theorem parsed_one {η : Nat} {L : List Zq} {X : List Byte} {done : Nat} (hd : done<X.length) :
    parsed η L X (done+1)=rbStep η (parsed η L X done) X[done]! := by
  rw [parsed,List.take_succ_eq_append_getElem hd,rbFold_append,getElem!_pos X done hd]
  rfl

theorem parsed_complete {η : Nat} {L : List Zq} {X : List Byte} {done : Nat}
    (he : done=X.length ∨ (parsed η L X done).length=256) :
    parsed η L X done=rbFold η L X := by
  rcases he with rfl|hfull
  · simp only [parsed,List.take_length]
  · have heq : rbFold η L X=rbFold η (parsed η L X done) (X.drop done) := by
      simp only [parsed]
      rw [←rbFold_append, List.take_append_drop]
    rw [heq,rbFold_full hfull]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourParseArgs`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Sample (movQ rbBound)

def scalarSetup (η : Nat) : List Instr :=
 [.movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6,
 .movz .x .x5 272 0]++movQ .x9++
 [.movz .x .x10 (BitVec.ofNat 16 η) 0,.movz .x .x11 15 0,
  .movz .x .x15 (BitVec.ofNat 16 (rbBound η)) 0]

private theorem count_shift : ∀j≤256,
    ((256#64-BitVec.ofNat 64 (256-j))<<<2)=BitVec.ofNat 64 (4*j) := by
  intro j hj
  have hs:=BitVec.ofNat_sub_ofNat_of_le (w := 64) 256 (256-j) (by omega_using []) (by omega_using [])
  rw [hs,show 256-(256-j)=j by omega_using [hj],BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 j * BitVec.ofNat 64 4=BitVec.ofNat 64 (4*j)
  rw [←BitVec.ofNat_mul,Nat.mul_comm]

structure ScalarReady (η : Nat) (p : Addr) (j : Nat) (s : State) : Prop where
 output : s.gpr .x3=VG.Proof.MlDsa.Sample.coeffAddr p j
 bytes : s.gpr .x5=272
 q : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q
 eta : s.gpr .x10=BitVec.ofNat 64 η
 mask : s.gpr .x11=15
 bound : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)

theorem scalarSetup_ok {s : State} {η j : Nat} (he : η=2∨η=4) (hj : j≤256)
    {p : Addr} (h3 : s.gpr .x3=p) (h4 : s.gpr .x4=BitVec.ofNat 64 (256-j)) :
    WP isa (.block (scalarSetup η)) s fun t=>
      InitKeep [.x3,.x5,.x6,.x9,.x10,.x11,.x15] [] s t ∧ ScalarReady η p j t := by
  have hh : WP isa (.block (scalarSetup η)) s fun t=>
      (ScalarReady η p j t ∧ t.mem=s.mem) ∧ Keep [.x3,.x5,.x6,.x9,.x10,.x11,.x15] s t := by
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
    rcases he with rfl|rfl <;>
      unfold scalarSetup movQ <;>
      arun [h3,h4,count_shift j hj,VG.Proof.MlDsa.Sample.coeffAddr]
    all_goals constructor <;> simp [State.write,Size.bits,VG.Proof.MlDsa.Sample.coeffAddr,
      count_shift j hj,Spec.MlDsa.q,VG.Proof.MlDsa.Sample.rbB,rbBound]
  refine WP.mono (WP.keepV (by rfl) hh) fun t ⟨⟨⟨hc,hm⟩,hk⟩,hv⟩=>
    ⟨⟨hk,hm,fun _ _=>congrFun hv _⟩,hc⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourScalarLoop`, which the modules that import this one used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourLoop`, which the modules that import this one used -/

section

/-! ## From `BoundedFourLoopState.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep)

structure Layout (σ : State) (table p q : Addr) (X : List Byte) : Prop where
 short : X.length≤272
 even : X.length%2=0
 stream : ∀i<X.length,σ.mem (q+BitVec.ofNat 64 i)=X[i]!
 streamApart : (⟨q,X.length+2⟩ : Region).Disjoint (polyR p)
 tableApart : (⟨table,1024⟩ : Region).Disjoint (polyR p)
 read : ∀d,d+2≤X.length→InRegions (σ.rd++σ.wr) (q+BitVec.ofNat 64 d) 4
 tableRead : ∀m<16,InRegions (σ.rd++σ.wr) (table+BitVec.ofNat 64 (64*m)) 16 ∧
      InRegions (σ.rd++σ.wr) (table+BitVec.ofNat 64 (64*m)+32) 8
 write : ∀j,j≤252→InRegions σ.wr (coeffAddr p j) 16

structure LoopInv (σ : State) (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte)
    (done : Nat) (s : State) : Prop where
 bound : done≤X.length
 even : done%2=0
 consts : Consts η table s
 table : TableAt s.mem table
 keep : Keep bodyRegs σ s
 frame : Frame [polyR p] σ.mem s.mem
 stored : Stored s.mem p (parsed η L X done)
 input : s.gpr .x2=q+BitVec.ofNat 64 done
 output : s.gpr .x3=coeffAddr p (parsed η L X done).length
 remaining : s.gpr .x4=BitVec.ofNat 64 (256-(parsed η L X done).length)
 bytes : s.gpr .x5=BitVec.ofNat 64 (X.length-done)
 guard : s.gpr .x8=if (parsed η L X done).length≤252 then BitVec.ofNat 64 (X.length-done) else 0

theorem LoopInv.stream {σ s : State} {η done : Nat} {table p q : Addr} {L : List Zq} {X : List Byte}
    (h : LoopInv σ η table p q L X done s) (hY : Layout σ table p q X) {i : Nat} (hi : i<X.length) :
    s.mem (q+BitVec.ofNat 64 i)=X[i]! := by
  rw [h.frame.bytes (R := ⟨q,X.length+2⟩) (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact hY.streamApart) (by change X.length+2≤2^64; have:=hY.short; omega_using [this]) (by change i<X.length+2; omega_using [hi])]
  exact hY.stream i hi

theorem LoopInv.values {σ s : State} {η done : Nat} {table p q : Addr} {L : List Zq} {X : List Byte}
    (h : LoopInv σ η table p q L X done s) (hY : Layout σ table p q X) (hd : done+2≤X.length) :
    bodyValues η s=accepted η (nibbles X[done]! X[done+1]!) := by
  unfold bodyValues
  rw [h.input,h.stream hY (by omega_using [hd])]
  have ha : q+BitVec.ofNat 64 done+1=q+BitVec.ofNat 64 (done+1) := by
    rw [BitVec.add_assoc,BitVec.ofNat_add]; rfl
  rw [ha,h.stream hY (by omega_using [hd])]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourLoopStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

theorem vectorLoopStep_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte}
    (hY : Layout σ table p q X) (h : LoopInv σ η table p q L X done s)
    (hd : done+2≤X.length) (hL : (parsed η L X done).length≤252) :
    WP isa (.block (vectorBody true η)) s (LoopInv σ η table p q L X (done+2)) := by
  refine WP.mono (vectorBody_ok hη h.consts h.table
    (fun m hm=>by rw [h.keep.rd,h.keep.wr]; exact hY.tableRead m hm)
    (by rw [h.keep.rd,h.keep.wr,h.input]; exact hY.read done hd)
    hL (by omega_using [hd]) h.stored h.output h.remaining h.bytes
    (by rw [h.keep.wr]; exact hY.write _ hL)) fun t ht=>?_
  have hl : parsed η L X (done+2)=parsed η L X done++bodyValues η s := by
    rw [parsed_two hη hd hL,h.values hY hd]
  have hbytes : X.length-(done+2)=(X.length-done)-2:=by omega_using []
  refine ⟨by omega_using [hd],by have:=h.even; omega_using [this],
    h.consts.body ht.keep ht.vectors,
    h.table.frame ht.frame (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hY.tableApart),
    (h.keep.trans ht.keep).mono ?_,h.frame.trans ht.frame,?_,?_,?_,?_,?_,?_⟩
  · intro r hr
    simpa only [List.mem_append,or_self] using hr
  · rw [hl]; exact ht.stored
  · rw [ht.input,h.input,BitVec.add_assoc,BitVec.ofNat_add]
    rfl
  · rw [hl]; exact ht.output
  · rw [hl]; exact ht.remaining
  · rw [hbytes]; exact ht.remainingBytes
  · rw [hl,hbytes]; exact ht.guard

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (eval_nonzero eval_zero ne_zero_iff eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorBody)

def VectorDone (σ : State) (η : Nat) (table p q : Addr) (L : List Zq) (X : List Byte)
    (s : State) : Prop := ∃done,LoopInv σ η table p q L X done s ∧
      (done=X.length ∨ 252<(parsed η L X done).length)

theorem loopGuard_eval {σ s : State} {η done : Nat} {table p q : Addr}
    {L : List Zq} {X : List Byte} (hY : Layout σ table p q X)
    (h : LoopInv σ η table p q L X done s) :
    isa.eval (.nonzero .x .x8) s=
      some (decide (done<X.length ∧ (parsed η L X done).length≤252)) := by
  rw [eval_nonzero,h.guard]
  by_cases hl : (parsed η L X done).length≤252
  · rw [ite_eq_left hl,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=hY.short; omega_using [this])]
    congr 1
    apply decide_eq_decide.mpr
    have:=h.bound
    omega_using [hl]
  · rw [ite_eq_right hl]
    simp only [hl,and_false,decide_false]
    rfl

theorem vectorLoop_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte}
    (hY : Layout σ table p q X) (h : LoopInv σ η table p q L X done s)
    (hd : done<X.length) (hl : (parsed η L X done).length≤252) :
    WP isa (.loop (.block (vectorBody true η)) (.nonzero .x .x8)) s
      (VectorDone σ η table p q L X) := by
  refine WP.loop (M := isa)
    (fun rank s=>∃d,rank=X.length-d ∧ LoopInv σ η table p q L X d s ∧
      d<X.length ∧ (parsed η L X d).length≤252) ?_ (X.length-done) s
      ⟨done,rfl,h,hd,hl⟩
  rintro rank u ⟨d,rfl,hu,hd,hl⟩
  have hd2 : d+2≤X.length:=by have:=hY.even; have:=hu.even; omega_arith
  refine WP.mono (vectorLoopStep_ok hη hY hu hd2 hl) fun v hv=>?_
  have he:=loopGuard_eval hY hv
  by_cases hc : d+2<X.length ∧ (parsed η L X (d+2)).length≤252
  · exact .inr ⟨by rw [he,decide_eq_true hc],X.length-(d+2),by omega_using [hd],
      d+2,rfl,hv,hc⟩
  · refine .inl ⟨by rw [he,decide_eq_false hc],d+2,hv,?_⟩
    omega_using [hd2, hc]

theorem loopGuard_zero {σ s : State} {η done : Nat} {table p q : Addr}
    {L : List Zq} {X : List Byte} (hY : Layout σ table p q X)
    (h : LoopInv σ η table p q L X done s) :
    isa.eval (.zero .x .x8) s=
      some (decide (done=X.length ∨ 252<(parsed η L X done).length)) := by
  rw [eval_zero,h.guard]
  by_cases hl : (parsed η L X done).length≤252
  · rw [ite_eq_left hl,eq_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=hY.short; omega_using [this])]
    congr 1
    apply decide_eq_decide.mpr
    have:=h.bound
    omega_using [hl, this]
  · rw [ite_eq_right hl]
    have hn : 252<(parsed η L X done).length:=by omega_using [hl]
    simp only [hn,or_true,decide_true]
    rfl

theorem vectorPhase_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte}
    (hY : Layout σ table p q X) (h : LoopInv σ η table p q L X done s) :
    WP isa (.ite (.zero .x .x8) (.block [])
      (.loop (.block (vectorBody true η)) (.nonzero .x .x8))) s
      (VectorDone σ η table p q L X) := by
  have hz:=loopGuard_zero hY h
  by_cases he : done=X.length ∨ 252<(parsed η L X done).length
  · exact WP.ite true (by rw [hz,decide_eq_true he])
      (fun _=>WP.block_nil_iff.mpr ⟨done,h,he⟩) (fun h=>nomatch h)
  · exact WP.ite false (by rw [hz,decide_eq_false he]) (fun h=>nomatch h)
      (fun _=>vectorLoop_ok hη hY h (by have:=h.bound; omega_using [he, this]) (by omega_using [he]))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourScalarBody.lean` -/

@[expose] public section

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
/-- What a batch's parse may write: the parser's registers and the loop's pointers. -/
abbrev batchRegs : List Reg := .x0::parserRegs++[.x24,.x25,.x26,.x27]

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
    rw [List.mem_singleton.mp hr]; exact hy.apart) (by change X.length≤2^64; have:=hy.short; omega_using [this]) hi]
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
    have hh:=BitVec.ofNat_sub_ofNat_of_le (w := 64) (X.length-done) 1 (by decide) (by omega_using [hd])
    change BitVec.ofNat 64 (X.length-done)-1#64=_
    simpa only [show X.length-done-1=X.length-(done+1) by omega_using []] using hh
  refine WP.mono (scalarGuard_ok htremaining ht5) fun u ⟨hu,h8⟩=>?_
  have hk : Keep parserRegs σ u :=
    ((hi.keep.trans htkeep).trans hu.keep).mono (by decide)
  refine ⟨by omega_using [hd],(hi.consts.keep htkeep (by decide)).keep hu.keep (by decide),hk,?_,?_,?_,?_,?_,?_,h8⟩
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
  have hn : X.length-done≤272 := by have:=hy.short; omega_using [this]
  have hp : (256-(parsed η L X done).length)*(X.length-done)<2^64 := by
    have:=Nat.mul_le_mul hr hn
    omega_using [this]
  rw [eval_nonzero,hi.guard,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
  congr 1
  apply decide_eq_decide.mpr
  rw [Nat.mul_ne_zero_iff]
  have:=hi.bound
  have:=parsed_bound (η := η) (X := X) hl done
  omega_using []

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
  · have hn : ¬(done<X.length ∧ (parsed η L X done).length<256) := by omega_using [he]
    simp only [decide_eq_false hn] at h
    have hz : s.gpr .x8=0 := by simpa using h
    simp [hz,he]
  · have hn : done<X.length ∧ (parsed η L X done).length<256 := by omega_using [hb, hd, he]
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
  · exact .inr ⟨by rw [he,decide_eq_true hc],X.length-(d+1),by omega_using [hd],d+1,rfl,hv,hc⟩
  · refine .inl ⟨by rw [he,decide_eq_false hc],d+1,hv,?_⟩
    have:=hv.bound
    have:=parsed_bound (η := η) (X := X) hl (d+1)
    omega_using [hd, hc, this]

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
      (fun _=>scalarLoop_ok hη hl hy hi (by have:=hi.bound; omega_using [hc, this])
        (by have:=parsed_bound (η := η) (X := X) hl done; omega_using [hc, this]))

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourInitMiddle.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def middleSetup : List Instr :=
 [.vop (.dup .b16 .v23 .x11),.vop (.dup .s4 .v22 .x15),.vop (.dup .s4 .v21 .x9),
 .vop (.dup .s4 .v20 .x10),.vop (.add .s4 .v20 .v20 .v21),.movz .x .x6 13 0,
 .vop (.dup .s4 .v18 .x6),.movz .x .x6 5 0,.vop (.dup .s4 .v19 .x6)]

def initWord (x : BitVec 32) : BitVec 128 := ofVWords x x x x

structure MiddleConstants (η : Nat) (s : State) : Prop where
 nibble : s.v .v23=ofVBytes (fun _=>15)
 bound : s.v .v22=initWord (BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η))
 q : s.v .v21=initWord 8380417
 etaQ : s.v .v20=initWord (BitVec.ofNat 32 (Spec.MlDsa.q+η))
 thirteen : s.v .v18=initWord 13
 five : s.v .v19=initWord 5

theorem middleSetup_ok {s : State} {η : Nat} (he : η=2∨η=4)
    (h9 : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q)
    (h10 : s.gpr .x10=BitVec.ofNat 64 η) (h11 : s.gpr .x11=15)
    (h15 : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)) :
    WP isa (.block middleSetup) s fun t=>
      InitKeep [.x6] [.v23,.v22,.v21,.v20,.v18,.v19] s t ∧ MiddleConstants η t := by
  unfold middleSetup
  refine wp_vop (d := .v23) rfl fun a ha=>wp_vop (d := .v22) rfl fun b hb=>
    wp_vop (d := .v21) rfl fun c hc=>wp_vop (d := .v20) rfl fun d hd=>
    wp_vop (d := .v20) rfl fun e he0=>?_
  refine wp_scalar (P := fun f=>Only [.x6] e f ∧ f.gpr .x6=13) (is := [.movz .x .x6 13 0]) rfl
    (wp_movz fun f hf h6=>wp_nil ⟨hf,h6⟩) fun f ⟨hf,h6⟩ hfv=>
    wp_vop (d := .v18) rfl fun g hg=>?_
  refine wp_scalar (P := fun h=>Only [.x6] g h ∧ h.gpr .x6=5) (is := [.movz .x .x6 5 0]) rfl
    (wp_movz fun h hh h5=>wp_nil ⟨hh,h5⟩) fun h ⟨hh,h5⟩ hhv=>
    wp_vop (d := .v19) rfl fun t ht=>wp_nil ?_
  have hk := ((((((((InitKeep.ofV ha (by decide)).trans (InitKeep.ofV hb (by decide))).trans
    (InitKeep.ofV hc (by decide))).trans (InitKeep.ofV hd (by decide))).trans
    (InitKeep.ofV he0 (by decide))).trans (InitKeep.ofOnly hf hfv)).trans
    (InitKeep.ofV hg (by decide))).trans (InitKeep.ofOnly hh hhv)).trans (InitKeep.ofV ht (by decide))
  refine ⟨hk.mono (by decide) (by decide),?_⟩
  constructor
  · rw [ht.other .v23 (by decide),hhv,hg.other .v23 (by decide),hfv,he0.other .v23 (by decide),hd.other .v23 (by decide),hc.other .v23 (by decide),hb.other .v23 (by decide),ha.v]
    rw [h11]
    rfl
  · rw [ht.other .v22 (by decide),hhv,hg.other .v22 (by decide),hfv,he0.other .v22 (by decide),hd.other .v22 (by decide),hc.other .v22 (by decide),hb.v]
    rw [ha.gpr,h15]
    rcases he with rfl|rfl <;> rfl
  · rw [ht.other .v21 (by decide),hhv,hg.other .v21 (by decide),hfv,he0.other .v21 (by decide),hd.other .v21 (by decide),hc.v]
    rw [hb.gpr,ha.gpr,h9]
    rfl
  · rw [ht.other .v20 (by decide),hhv,hg.other .v20 (by decide),hfv,he0.v]
    rw [hd.v,hd.other .v21 (by decide),hc.v,hc.gpr,hb.gpr,ha.gpr,h10,h9]
    rcases he with rfl|rfl <;> rfl
  · rw [ht.other .v18 (by decide),hhv,hg.v]
    rw [h6]
    rfl
  · rw [ht.v]
    rw [h5]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (vectorSetup)

def setupFooter : List Instr :=
 [.movz .x .x0 0 0,.movz .x .x16 4 0,.addImm .x .x12 .x19 3000,.addImm .x .x12 .x12 3000]

theorem setupFooter_ok (s : State) :
    WP isa (.block setupFooter) s fun t=>InitKeep [.x0,.x16,.x12] [] s t ∧
      t.gpr .x0=0 ∧ t.gpr .x16=4 ∧ t.gpr .x12=s.gpr .x19+6000 := by
  let P : State→Prop := fun t=>Only [.x0,.x16,.x12] s t ∧
    t.gpr .x0=0 ∧ t.gpr .x16=4 ∧ t.gpr .x12=s.gpr .x19+6000
  apply WP.mono (WP.keepV (is := setupFooter) (Q := P) (by decide) ?_)
  · intro t ⟨⟨ho,h0,h16,h12⟩,hv⟩
    exact ⟨InitKeep.ofOnly ho hv,h0,h16,h12⟩
  change WP isa (.block setupFooter) s P
  dsimp only [P]
  unfold setupFooter
  refine wp_movz fun a ha h0=>wp_movz fun b hb h16=>
    wp_addImm (by decide) fun c hc h12=>wp_addImm (by decide) fun t ht h12'=>wp_nil ?_
  refine ⟨(((ha.trans hb).trans hc).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x0,hc.get .x0,hb.get .x0,h0]; rfl
  · rw [ht.get .x16,hc.get .x16,h16]; rfl
  · rw [h12',h12,hb.get .x19,ha.get .x19,BitVec.add_assoc]; rfl

theorem vectorSetup_eq (η : Nat) : vectorSetup η=
    pairSetup .v25 0xffffff01ffffff00 0xffffff03ffffff02 ++ middleSetup ++
      pairSetup .v24 0x0000000200000001 0x0000000800000004 ++ setupFooter := rfl

theorem initWord_lane (x : BitVec 32) {e : Nat} (he : e<4) : vword (initWord x) e=x := by
  unfold initWord
  rw [VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
  rcases (show e=0∨e=1∨e=2∨e=3 by omega_using [he]) with rfl|rfl|rfl|rfl <;> rfl

private theorem weights_lane : ∀e<4,
    vword (ofVDwords 0x0000000200000001 0x0000000800000004) e=BitVec.ofNat 32 (2^e) := by decide

theorem vectorSetup_ok {s : State} {η : Nat} (he : η=2∨η=4)
    (h9 : s.gpr .x9=BitVec.ofNat 64 Spec.MlDsa.q)
    (h10 : s.gpr .x10=BitVec.ofNat 64 η) (h11 : s.gpr .x11=15)
    (h15 : s.gpr .x15=BitVec.ofNat 64 (VG.Proof.MlDsa.Sample.rbB η)) :
    WP isa (.block (vectorSetup η)) s fun t=>
      InitKeep [.x0,.x6,.x7,.x12,.x16] constantVecs s t ∧ Consts η (s.gpr .x19+6000) t := by
  rw [vectorSetup_eq,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pairSetup_ok s .v25 _ _ (by decide)) fun a ⟨ha,h25⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (middleSetup_ok he (by rw [ha.keep.gpr .x9 (by decide)]; exact h9)
    (by rw [ha.keep.gpr .x10 (by decide)]; exact h10)
    (by rw [ha.keep.gpr .x11 (by decide)]; exact h11)
    (by rw [ha.keep.gpr .x15 (by decide)]; exact h15)) fun b ⟨hb,hbC⟩=>?_
  rw [WP.block_append_iff]
  refine WP.mono (pairSetup_ok b .v24 _ _ (by decide)) fun c ⟨hc,h24⟩=>?_
  refine WP.mono (setupFooter_ok c) fun t ⟨ht,h0,h16,h12⟩=>?_
  have hk := ((ha.trans hb).trans hc).trans ht
  have hc19 : c.gpr .x19=s.gpr .x19 := ((ha.trans hb).trans hc).keep.gpr _ (by decide)
  refine ⟨hk.mono (by decide) (by decide),?_⟩
  constructor
  · exact h0
  · rw [hk.keep.gpr .x11 (by decide)]; exact h11
  · rw [h12,hc19]
  · exact h16
  · intro e he
    rw [ht.vec .v18 (by decide),hc.vec .v18 (by decide),hbC.thirteen,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v19 (by decide),hc.vec .v19 (by decide),hbC.five,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v20 (by decide),hc.vec .v20 (by decide),hbC.etaQ,initWord_lane _ he]
  · intro e he
    rw [ht.vec .v21 (by decide),hc.vec .v21 (by decide),hbC.q,initWord_lane _ he]
    rfl
  · intro e he
    rw [ht.vec .v22 (by decide),hc.vec .v22 (by decide),hbC.bound,initWord_lane _ he]
  · rw [ht.vec .v23 (by decide),hc.vec .v23 (by decide),hbC.nibble]
  · intro e he
    rw [ht.vec .v24 (by decide),h24]
    exact weights_lane e he
  · rw [ht.vec .v25 (by decide),hc.vec .v25 (by decide),hb.vec .v25 (by decide),h25]
    rfl
  · rw [hk.keep.gpr .x9 (by decide)]; exact h9
  · rw [hk.keep.gpr .x10 (by decide)]; exact h10
  · rw [hk.keep.gpr .x15 (by decide)]; exact h15

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
