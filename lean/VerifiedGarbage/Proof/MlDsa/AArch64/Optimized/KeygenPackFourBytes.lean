module

public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.AArch64.Optimized.KeygenPackFourMath`, which this module and modules that import it used -/

section

/-! ## From `KeygenPackFourMachine.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def fourGather (v : VReg → BitVec 128) (idx : BitVec 128) : BitVec 128 :=
  ofVBytes fun i=>let j:=(vbyte idx i).toNat; if j<64 then tableByte v .v0 j else 0

def fourShift (x : BitVec 128) (n : Nat) : BitVec 128 :=
  VArr.s4.map2 (fun _ _ y=>y >>> n) x x

def fourCompress (x mask idx : BitVec 128) : BitVec 128 :=
  let a := (x ||| fourShift x 4) &&& mask
  let b := a ||| fourShift a 8
  ofVBytes fun i=>let j:=(vbyte idx i).toNat; if j<16 then vbyte b j else 0

def fourShuffle : List Instr :=
  [.vop (.tblN false 4 .v0 .v0 .v18),.vop (.shift .ushr .s4 .v1 .v0 4),
   .vop (.logic .orr .v0 .v0 .v1),.vop (.logic .and .v0 .v0 .v20),
   .vop (.shift .ushr .s4 .v1 .v0 8),.vop (.logic .orr .v0 .v0 .v1),
   .vop (.tbl .v0 .v0 .v19)]

theorem fourShuffle_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg [.v0,.v1] s t →
      t.v .v0=fourCompress (fourGather s.v (s.v .v18)) (s.v .v20) (s.v .v19) →
      WP isa (.block rest) t Q) :
    WP isa (.block (fourShuffle++rest)) s Q := by
  refine wp_vop (d:=.v0) rfl fun a ha=>wp_vop (d:=.v1) rfl fun b hb=>
    wp_vop (d:=.v0) rfl fun c hc=>wp_vop (d:=.v0) rfl fun d hd=>
    wp_vop (d:=.v1) rfl fun e he=>wp_vop (d:=.v0) rfl fun f hf=>
    wp_vop (d:=.v0) rfl fun t ht=>?_
  refine k t (((((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans he.chg).trans hf.chg).trans ht.chg).mono (by simp)) ?_
  rw [ht.v,hf.v,he.get .v0 (by decide),he.v,hd.v,hc.v,hb.get .v0 (by decide),hb.v,ha.v,
    hf.get .v19 (by decide),he.get .v19 (by decide),hd.get .v19 (by decide),hc.get .v19 (by decide),
    hb.get .v19 (by decide),ha.get .v19 (by decide),hc.get .v20 (by decide),hb.get .v20 (by decide),ha.get .v20 (by decide)]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackFourMath.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64

def fourGatherIndex : BitVec 128 := ofVBytes fun i=>BitVec.ofNat 8 (4*i)
def fourPackIndex : BitVec 128 := ofVBytes fun i=>
  if i<8 then BitVec.ofNat 8 (4*(i/2)+i%2) else 255

theorem fourGather_byte (v : VReg → BitVec 128) {i : Nat} (hi : i<16) :
    vbyte (fourGather v fourGatherIndex) i=tableByte v .v0 (4*i) := by
  rw [fourGather,vbyte_ofVBytes _ hi]
  simp only [fourGatherIndex,vbyte_ofVBytes _ hi,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_using [hi] : 4*i<2^8),ite_eq_left (by omega_using [hi])]

/-- Four separate byte-sized nibbles become two packed bytes in the low half. -/
theorem four_word (a b c d : BitVec 4) :
    let x : BitVec 32 := a.setWidth 32 ||| (b.setWidth 32 <<< 8) |||
      (c.setWidth 32 <<< 16) ||| (d.setWidth 32 <<< 24)
    let y := (x ||| (x >>> 4)) &&& 0x00ff00ff
    ((y ||| (y >>> 8)).setWidth 16) =
      a.setWidth 16 ||| (b.setWidth 16 <<< 4) ||| (c.setWidth 16 <<< 8) ||| (d.setWidth 16 <<< 12) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 by omega_using [hi]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem fourCompress_byte (x mask : BitVec 128) {i : Nat} (hi : i<16) :
    vbyte (fourCompress x mask fourPackIndex) i=
      if i<8 then vbyte (((x ||| fourShift x 4) &&& mask) |||
        fourShift ((x ||| fourShift x 4) &&& mask) 8) (4*(i/2)+i%2) else 0 := by
  rw [fourCompress,vbyte_ofVBytes _ hi]
  simp only [fourPackIndex,vbyte_ofVBytes _ hi]
  by_cases h : i<8
  · rw [ite_eq_left h,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hi] : 4*(i/2)+i%2<2^8),
      ite_eq_left (by omega_using [h]),ite_eq_left h]
  · rw [ite_eq_right h,ite_eq_right h]
    rfl

theorem fourShift_word (x : BitVec 128) (n : Nat) {e : Nat} (he : e<4) :
    vword (fourShift x n) e=vword x e >>> n := by
  exact VG.AArch64.vword_map2 _ _ _ he

theorem fourWord_low (x : BitVec 128) {e : Nat} (he : e<4) (a b c d : BitVec 4)
    (hx : vword x e=a.setWidth 32 ||| (b.setWidth 32 <<< 8) |||
      (c.setWidth 32 <<< 16) ||| (d.setWidth 32 <<< 24))
    (mask : BitVec 128) (hm : vword mask e=0x00ff00ff) :
    (vword (((x ||| fourShift x 4) &&& mask) |||
      fourShift ((x ||| fourShift x 4) &&& mask) 8) e).setWidth 16 =
      a.setWidth 16 ||| (b.setWidth 16 <<< 4) ||| (c.setWidth 16 <<< 8) ||| (d.setWidth 16 <<< 12) := by
  simp only [vword,BitVec.extractLsb'_or,BitVec.extractLsb'_and]
  change (((vword x e ||| vword (fourShift x 4) e) &&& vword mask e) |||
    vword (fourShift ((x ||| fourShift x 4) &&& mask) 8) e).setWidth 16=_
  rw [fourShift_word _ _ he,fourShift_word _ _ he]
  have hh : vword ((x ||| fourShift x 4) &&& mask) e=
      (vword x e ||| vword (fourShift x 4) e) &&& vword mask e := by
    simp only [vword,BitVec.extractLsb'_or,BitVec.extractLsb'_and]
  rw [hh,fourShift_word _ _ he,hx,hm]
  exact four_word a b c d

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64

theorem four_word_byte (x : BitVec 128) {e j : Nat} (hj : j<4) :
    (vword x e).extractLsb' (8*j) 8=vbyte x (4*e+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vword,vbyte,BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and,
    show 8*j+k<32 by omega_arith]
  congr 1
  omega_arith

theorem fourGather_coeff (v : VReg → BitVec 128) (f : Nat → BitVec 4)
    (h : ∀i<16,tableByte v .v0 (4*i)=(f i).setWidth 8) {e : Nat} (he : e<4) :
    vword (fourGather v fourGatherIndex) e=
      (f (4*e)).setWidth 32 ||| ((f (4*e+1)).setWidth 32 <<< 8) |||
      ((f (4*e+2)).setWidth 32 <<< 16) ||| ((f (4*e+3)).setWidth 32 <<< 24) := by
  have hb (j : Nat) (hj : j<4) :
      (vword (fourGather v fourGatherIndex) e).extractLsb' (8*j) 8=(f (4*e+j)).setWidth 8 := by
    rw [four_word_byte _ hj,fourGather_byte _ (by omega_arith),h _ (by omega_arith)]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 ∨ k=19 ∨ k=20 ∨ k=21 ∨ k=22 ∨ k=23 ∨ k=24 ∨ k=25 ∨ k=26 ∨ k=27 ∨ k=28 ∨ k=29 ∨ k=30 ∨ k=31 by omega_arith) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 0 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 1 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 2 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 0) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 1) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 2) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 3) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 4) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 5) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 6) (hb 3 (by decide))
  · simpa using congrArg (fun z : BitVec 8=>z.getLsbD 7) (hb 3 (by decide))

theorem four_word_low_byte (x : BitVec 128) {e j : Nat} (hj : j<2) :
    ((vword x e).setWidth 16).extractLsb' (8*j) 8=vbyte x (4*e+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hk,decide_true,Bool.true_and,
    show 8*j+k<16 by omega_arith,vword,vbyte,show 8*j+k<32 by omega_arith]
  congr 1
  omega_arith

theorem four_packed_byte (a b c d : BitVec 4) {j : Nat} (hj : j<2) :
    (a.setWidth 16 ||| (b.setWidth 16 <<< 4) ||| (c.setWidth 16 <<< 8) |||
      (d.setWidth 16 <<< 12)).extractLsb' (8*j) 8 =
      if j=0 then a.setWidth 8 ||| (b.setWidth 8 <<< 4) else c.setWidth 8 ||| (d.setWidth 8 <<< 4) := by
  rcases (show j=0 ∨ j=1 by omega_arith) with rfl|rfl
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro k hk
  all_goals rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 by omega_arith) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem four_output_byte (v : VReg → BitVec 128) (f : Nat → BitVec 4)
    (h : ∀i<16,tableByte v .v0 (4*i)=(f i).setWidth 8)
    (mask : BitVec 128) (hm : ∀e<4,vword mask e=0x00ff00ff) {i : Nat} (hi : i<8) :
    vbyte (fourCompress (fourGather v fourGatherIndex) mask fourPackIndex) i=
      (f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4) := by
  rw [fourCompress_byte _ _ (by omega_arith),ite_eq_left hi,
    ← four_word_low_byte _ (by omega_arith : i%2<2),
    fourWord_low _ (by omega_arith : i/2<4) _ _ _ _ (fourGather_coeff v f h (by omega_arith)) mask (hm _ (by omega_arith)),
    four_packed_byte _ _ _ _ (by omega_arith)]
  rcases (show i%2=0 ∨ i%2=1 by omega_arith) with hz|hz
  · rw [ite_eq_left hz]
    rw [show 4*(i/2)=2*i by omega_arith]
  · rw [ite_eq_right (by omega_arith)]
    rw [show 4*(i/2)+2=2*i by omega_arith,show 4*(i/2)+3=2*i+1 by omega_arith]

theorem fourShuffle_bytes {s : State} {rest : List Instr} {Q : State → Prop}
    (f : Nat → BitVec 4) (hg : s.v .v18=fourGatherIndex) (hp : s.v .v19=fourPackIndex)
    (hm : ∀e<4,vword (s.v .v20) e=0x00ff00ff)
    (hf : ∀i<16,tableByte s.v .v0 (4*i)=(f i).setWidth 8)
    (k : ∀t,VG.Proof.MlKem.AArch64.VChg [.v0,.v1] s t →
      (∀i<8,vbyte (t.v .v0) i=(f (2*i)).setWidth 8 ||| ((f (2*i+1)).setWidth 8 <<< 4)) →
      WP isa (.block rest) t Q) : WP isa (.block (fourShuffle++rest)) s Q := by
  refine fourShuffle_ok fun t ht hout=>k t ht ?_
  intro i hi
  rw [hout,hg,hp]
  exact four_output_byte s.v f hf (s.v .v20) hm hi

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
