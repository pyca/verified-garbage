module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLane
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckModel
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalAdvance
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame
import VerifiedGarbage.Proof.MlKem.Arith
import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Data.Fintype.Fin

/-! ### `MlDsa.AArch64.Optimized.PairedLowPair`, which only this module used -/

section

/-! ## `PairedLowHf2` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (raw)

def lowHfTwo (g : Nat) (a b : VReg) : List Instr :=
 ((lowHf g .v26 a).zip (lowHf g .v28 b)).flatMap fun (x,y) => [x,y]

theorem lowHfTwo_ok {g : Nat} (hg : IsG g) {a b : VReg} (hb : b≠.v26)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (k : ∀v,VChg [.v26,.v28] s v →
      (∀e<4,vword (v.v .v26) e=raw g (vword (s.v a) e)) →
      (∀e<4,vword (v.v .v28) e=raw g (vword (s.v b) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowHfTwo g a b++rest)) s Q := by
  have hsh : VShiftOp.ushr.ok VArr.s4.esize (dShift g) = true := by
    rcases hg with rfl | rfl <;> rfl
  refine wp_vop (d := .v26) rfl fun s1 h1 => ?_
  refine wp_vop (d := .v28) rfl fun s2 h2 => ?_
  refine wp_vop (d := .v26) rfl fun s3 h3 => ?_
  refine wp_vop (d := .v28) rfl fun s4 h4 => ?_
  refine wp_vop (d := .v26) rfl fun s5 h5 => ?_
  refine wp_vop (d := .v28) rfl fun s6 h6 => ?_
  refine wp_vop (d := .v26) rfl fun s7 h7 => ?_
  refine wp_vop (d := .v28) rfl fun s8 h8 => ?_
  refine wp_vop (d := .v26) (by simp only [VOp.eval,hsh,ite_true]; rfl) fun s9 h9 => ?_
  refine wp_vop (d := .v28) (by simp only [VOp.eval,hsh,ite_true]; rfl) fun s10 h10 => ?_
  refine k s10 ((((((((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg).trans h9.chg).trans h10.chg).mono (by simp)) ?_ ?_
  · intro e he
    have w1 : vword (s1.v .v26) e = vword (s.v a) e + BitVec.ofNat 32 127 := by
      rw [h1.v, VG.AArch64.vword_map2 _ _ _ he, h11 e he]
    have w3 : vword (s3.v .v26) e = (vword (s.v a) e + BitVec.ofNat 32 127) >>> 7 := by
      rw [h3.v, VG.AArch64.vword_map2 _ _ _ he, h2.get .v26 (by decide), w1]
      rfl
    have w5 : vword (s5.v .v26) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) := by
      rw [h5.v, VG.AArch64.vword_map2 _ _ _ he, h4.get .v26 (by decide), w3, h4.get .v12 (by decide), h3.get .v12 (by decide), h2.get .v12 (by decide), h1.get .v12 (by decide), h12 e he]
    have w7 : vword (s7.v .v26) e = ((vword (s.v a) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) + BitVec.ofNat 32 (hbAdd g) := by
      rw [h7.v, VG.AArch64.vword_map2 _ _ _ he, h6.get .v26 (by decide), w5, h6.get .v13 (by decide), h5.get .v13 (by decide), h4.get .v13 (by decide), h3.get .v13 (by decide), h2.get .v13 (by decide), h1.get .v13 (by decide), h13 e he]
    rw [h10.get .v26 (by decide), h9.v, VG.AArch64.vword_map2 _ _ _ he, h8.get .v26 (by decide), w7]
    rfl
  · intro e he
    have w2 : vword (s2.v .v28) e = vword (s.v b) e + BitVec.ofNat 32 127 := by
      rw [h2.v, VG.AArch64.vword_map2 _ _ _ he, h1.get b hb, h1.get .v11 (by decide), h11 e he]
    have w4 : vword (s4.v .v28) e = (vword (s.v b) e + BitVec.ofNat 32 127) >>> 7 := by
      rw [h4.v, VG.AArch64.vword_map2 _ _ _ he, h3.get .v28 (by decide), w2]
      rfl
    have w6 : vword (s6.v .v28) e = ((vword (s.v b) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) := by
      rw [h6.v, VG.AArch64.vword_map2 _ _ _ he, h5.get .v28 (by decide), w4, h5.get .v12 (by decide), h4.get .v12 (by decide), h3.get .v12 (by decide), h2.get .v12 (by decide), h1.get .v12 (by decide), h12 e he]
    have w8 : vword (s8.v .v28) e = ((vword (s.v b) e + BitVec.ofNat 32 127) >>> 7) * BitVec.ofNat 32 (hbMul g) + BitVec.ofNat 32 (hbAdd g) := by
      rw [h8.v, VG.AArch64.vword_map2 _ _ _ he, h7.get .v28 (by decide), w6, h7.get .v13 (by decide), h6.get .v13 (by decide), h5.get .v13 (by decide), h4.get .v13 (by decide), h3.get .v13 (by decide), h2.get .v13 (by decide), h1.get .v13 (by decide), h13 e he]
    rw [h10.v, VG.AArch64.vword_map2 _ _ _ he, h9.get .v28 (by decide), w8]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowWrap2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Impl.MlDsa.AArch64.Round

def lowWrap (g : Nat) (d t : VReg) : List Instr :=
 if g==261888 then [.vop (.logic .and d d .v14)] else
 [.vop (.sub .s4 t d .v14),.vop (.shift .sshr .s4 t t 31),.vop (.logic .and d d t)]
def lowWrapWord (g : Nat) (w : BitVec 32) : BitVec 32 :=
 if g==261888 then w &&& 15 else w &&& BitVec.sshiftRight (w-BitVec.ofNat 32 (dMod g)) 31

def lowWrapTwo (g : Nat) (q : VReg) : List Instr :=
 ((lowWrap g .v26 .v25).zip (lowWrap g .v28 q)).flatMap fun (x,y) => [x,y]

theorem lowWrapTwo_ok {g : Nat} {q : VReg}
    (hq25 : q≠.v25) (hq26 : q≠.v26) (hq28 : q≠.v28)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v,VChg [.v25,q,.v26,.v28] s v →
      (∀e<4,vword (v.v .v26) e=lowWrapWord g (vword (s.v .v26) e)) →
      (∀e<4,vword (v.v .v28) e=lowWrapWord g (vword (s.v .v28) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowWrapTwo g q++rest)) s Q := by
  unfold lowWrapTwo lowWrap
  by_cases hg : g==261888
  · simp only [hg,ite_true,List.zip_cons_cons,List.zip_nil_left,List.flatMap_cons,List.flatMap_nil,
      List.cons_append,List.nil_append]
    refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v28) rfl fun s2 h2 =>
      k s2 ((h1.chg.trans h2.chg).mono (by simp)) ?_ ?_
    · intro e he
      rw [h2.get .v26 (by decide),h1.v,Inverse.word_and,h14 e he]
      simp only [lowWrapWord,hg,ite_true]
      rfl
    · intro e he
      rw [h2.v,Inverse.word_and,h1.get .v28 (by decide),h1.get .v14 (by decide),h14 e he]
      simp only [lowWrapWord,hg,ite_true]
      rfl
  · simp only [hg]
    refine wp_vop (d := .v25) rfl fun s1 h1 => wp_vop (d := q) rfl fun s2 h2 =>
      wp_vop (d := .v25) rfl fun s3 h3 => wp_vop (d := q) rfl fun s4 h4 =>
      wp_vop (d := .v26) rfl fun s5 h5 => wp_vop (d := .v28) rfl fun s6 h6 => ?_
    refine k s6 (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg |>.mono (by simp)) ?_ ?_
    · intro e he
      rw [h6.get .v26 (by decide),h5.v,Inverse.word_and,
        h4.get .v26 (Ne.symm hq26),h3.get .v26 (by decide),h2.get .v26 (Ne.symm hq26),h1.get .v26 (by decide),
        h4.get .v25 (Ne.symm hq25),h3.v,VG.AArch64.vword_map2 _ _ _ he,
        h2.get .v25 (Ne.symm hq25),h1.v,VG.AArch64.vword_map2 _ _ _ he,h14 e he]
      simp only [lowWrapWord,hg]
      rfl
    · intro e he
      rw [h6.v,Inverse.word_and,
        h5.get .v28 (by decide),h4.get .v28 (Ne.symm hq28),h3.get .v28 (by decide),h2.get .v28 (Ne.symm hq28),h1.get .v28 (by decide),
        h5.get q hq26,h4.v,VG.AArch64.vword_map2 _ _ _ he,
        h3.get q hq25,h2.v,VG.AArch64.vword_map2 _ _ _ he,
        h1.get .v28 (by decide),h1.get .v14 (by decide),h14 e he]
      simp only [lowWrapWord,hg]
      rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowNorm2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (normMask minMask)

theorem norm_word_or (a b : BitVec 128) (e : Nat) :
    vword (a ||| b) e=vword a e ||| vword b e := by
  simp only [vword,BitVec.extractLsb'_or]

def normTwo (r q : VReg) : List Instr :=
 ((normRegs .v24 .v25).zip (normRegs r q)).flatMap fun (x,y) => [x,y]

/-- Both alternating norm checks contribute to the shared rejection flag. -/
theorem normTwo_ok {r q : VReg} (hr25 : r≠.v25)
    (hq25 : q≠.v25) (hq10 : q≠.v10) (hq30 : q≠.v30)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀v,VChg [.v25,q,.v30] s v →
      (∀e<4,vword (v.v .v30) e=
        (vword (s.v .v30) e ||| normMask (vword (s.v .v24) e) (vword (s.v .v9) e) (vword (s.v .v10) e)) |||
        normMask (vword (s.v r) e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (normTwo r q++rest)) s Q := by
  refine wp_vop (d := .v25) rfl fun s1 h1 => wp_vop (d := q) rfl fun s2 h2 =>
    wp_vop (d := .v25) rfl fun s3 h3 => wp_vop (d := q) rfl fun s4 h4 =>
    wp_vop (d := .v25) rfl fun s5 h5 => wp_vop (d := q) rfl fun s6 h6 =>
    wp_vop (d := .v30) rfl fun s7 h7 => wp_vop (d := .v30) rfl fun s8 h8 => ?_
  refine k s8 (((((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg |>.mono (by simp)) ?_
  intro e he
  have wa : vword (s5.v .v25) e=normMask (vword (s.v .v24) e) (vword (s.v .v9) e) (vword (s.v .v10) e) := by
    rw [h5.v,VG.AArch64.vword_map2 _ _ _ he,h4.get .v25 (Ne.symm hq25),
      h3.v,VG.AArch64.vword_map2 _ _ _ he,h2.get .v25 (Ne.symm hq25),h1.v,VG.AArch64.vword_map2 _ _ _ he,
      h4.get .v10 (Ne.symm hq10),h3.get .v10 (by decide),h2.get .v10 (Ne.symm hq10),h1.get .v10 (by decide),minMask]
    rfl
  have wb : vword (s6.v q) e=normMask (vword (s.v r) e) (vword (s.v .v9) e) (vword (s.v .v10) e) := by
    rw [h6.v,VG.AArch64.vword_map2 _ _ _ he,h5.get q hq25,
      h4.v,VG.AArch64.vword_map2 _ _ _ he,h3.get q hq25,h2.v,VG.AArch64.vword_map2 _ _ _ he,
      h1.get r hr25,h1.get .v9 (by decide),
      h5.get .v10 (by decide),h4.get .v10 (Ne.symm hq10),h3.get .v10 (by decide),h2.get .v10 (Ne.symm hq10),h1.get .v10 (by decide),minMask]
    rfl
  rw [h8.v,norm_word_or,h7.v,norm_word_or,
    h7.get q hq30,wb,h6.get .v25 (Ne.symm hq25),wa,
    h6.get .v30 (Ne.symm hq30),h5.get .v30 (by decide),h4.get .v30 (Ne.symm hq30),
    h3.get .v30 (by decide),h2.get .v30 (Ne.symm hq30),h1.get .v30 (by decide)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowStore2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_strq wp_vop VChg vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def storeTwo (a b : VReg) (n : Reg) (off : Nat) : List Instr :=
 [.strq a n off,.strq b n (off+128)]

theorem storeTwo_ok {a b : VReg} {n : Reg} {off : Nat}
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (hr : InRegions s.wr (s.gpr n+BitVec.ofNat 64 off) 16)
    (hr' : InRegions s.wr (s.gpr n+BitVec.ofNat 64 (off+128)) 16)
    (k : ∀v,StepKeep [] s v → v.v=s.v →
      v.mem=(s.mem.write (s.gpr n+BitVec.ofNat 64 off) 16 (s.v a)).write
        (s.gpr n+BitVec.ofNat 64 (off+128)) 16 (s.v b) → WP isa (.block rest) v Q) :
    WP isa (.block (storeTwo a b n off++rest)) s Q := by
  refine wp_strq (by omega_using [ho]) rfl hr fun u hu =>
    wp_strq (by omega_using [ho]) rfl (by rw [hu.wr,hu.gpr]; exact hr') fun v hv =>
      k v (((StepKeep.ofMem hu).trans (StepKeep.ofMem hv)).mono (by simp)) (hv.v.trans hu.v) ?_
  rw [hv.mem,hu.mem,hu.gpr,hu.v]

def mlsTwo (r : VReg) : List Instr :=
 [.vop (.mls .v24 .v26 .v15),.vop (.mls r .v28 .v15)]

theorem mlsTwo_ok {r : VReg} (hr : r≠.v24)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀v,VChg [.v24,r] s v →
      (∀e<4,vword (v.v .v24) e=vword (s.v .v24) e-vword (s.v .v26) e*vword (s.v .v15) e) →
      (∀e<4,vword (v.v r) e=vword (s.v r) e-vword (s.v .v28) e*vword (s.v .v15) e) →
      WP isa (.block rest) v Q) :
    WP isa (.block (mlsTwo r++rest)) s Q := by
  refine wp_vop (d := .v24) rfl fun u hu => wp_vop (d := r) rfl fun v hv =>
    k v ((hu.chg.trans hv.chg).mono (by simp)) ?_ ?_
  · intro e he
    rw [hv.get .v24 (Ne.symm hr),hu.v,vword_mapWords3 _ _ _ _ he]
  · intro e he
    rw [hv.v,vword_mapWords3 _ _ _ _ he,hu.get r hr,
      hu.get .v28 (by decide),hu.get .v15 (by decide)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowBlocks` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Proof-sized blocks in the original alternating instruction order. -/
def lowPairBlocks (g : Nat) (r q : VReg) (off : Nat) : List Instr :=
 lowLoadTwo r q off ++ reduceTwo .v24 .v25 r q ++ caddTwo .v24 .v25 r q ++
 lowHfTwo g .v24 r ++ lowWrapTwo g q ++ storeTwo .v26 .v28 .x15 off ++
 mlsTwo r ++ reduceTwo .v24 .v25 r q ++ storeTwo .v24 r .x16 off ++ normTwo r q

/-- No instruction, register reuse, or shared-flag update changes in this partition. -/
theorem r0Pair_blocks (g p j : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Pair g p j =
      lowPairBlocks g (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.vr (8*p+2*j))
        (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.vr (8*p+2*j+1)) (1024*p+256*j) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Pair
    VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane lowPairBlocks
    lowLoadTwo reduceTwo caddTwo lowHfTwo lowWrapTwo storeTwo mlsTwo normTwo
    reduceRegs lowCadd lowHf lowWrap normRegs
  by_cases hg : g==261888 <;>
    simp only [hg, ite_true, Bool.false_eq_true, ite_false, List.zip_cons_cons, List.zip_nil_left,
      List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowHb2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

theorem lowWrap_raw (g : Nat) (a : BitVec 32) :
    lowWrapWord g (HighPack.raw g a)=lowHighWord g a := by
  unfold lowWrapWord lowHighWord HighPack.highWord
  split <;> rfl

def lowHbTwo (g : Nat) (r q : VReg) : List Instr := lowHfTwo g .v24 r ++ lowWrapTwo g q

theorem lowHbTwo_ok {g : Nat} (hg : IsG g) {r q : VReg}
    (hr26 : r≠.v26) (hq25 : q≠.v25) (hq26 : q≠.v26) (hq28 : q≠.v28)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v,VChg [.v25,q,.v26,.v28] s v →
      (∀e<4,vword (v.v .v26) e=lowHighWord g (vword (s.v .v24) e)) →
      (∀e<4,vword (v.v .v28) e=lowHighWord g (vword (s.v r) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowHbTwo g r q++rest)) s Q := by
  unfold lowHbTwo
  rw [List.append_assoc]
  refine lowHfTwo_ok hg hr26 h11 h12 h13 fun u hu ha hb => ?_
  refine lowWrapTwo_ok hq25 hq26 hq28
    (by intro e he; rw [hu.get .v14 (by decide)]; exact h14 e he)
    fun v hv hva hvb => k v ((hu.trans hv).mono (by simp)) ?_ ?_
  · intro e he; rw [hva e he,ha e he,lowWrap_raw]
  · intro e he; rw [hvb e he,hb e he,lowWrap_raw]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowInput2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def lowReserved : List VReg :=
 [.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15,.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31]

def lowInputTwo (r q : VReg) (off : Nat) : List Instr :=
 lowLoadTwo r q off ++ reduceTwo .v24 .v25 r q ++ caddTwo .v24 .v25 r q

theorem lowInputTwo_ok {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (hread : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hread' : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v,VChg [.v27,.v29,.v24,.v25,r,q] s v →
      (∀e<4,vword (v.v .v24) e=lowInputWord s r off e) →
      (∀e<4,vword (v.v r) e=lowInputWord s q (off+128) e) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowInputTwo r q off++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  have hr24 := rn .v24 (by decide)
  have hr25 := rn .v25 (by decide)
  have hq24 := qn .v24 (by decide)
  have hq25 := qn .v25 (by decide)
  have hregs : ∀d∈[.v24,.v25,r,q],d≠.v8 ∧ d≠.v31 := by
    intro d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact ⟨rn .v8 (by decide),rn .v31 (by decide)⟩
    · exact ⟨qn .v8 (by decide),qn .v31 (by decide)⟩
  unfold lowInputTwo
  simp only [List.append_assoc]
  refine lowLoadTwo_ok hr24 (rn .v27 (by decide)) (rn .v29 (by decide))
    hq24 (qn .v27 (by decide)) (qn .v29 (by decide)) ho hread hread' fun u hu ha hb => ?_
  have huq : u.v .v31=s.v .v31 := hu.get .v31 (by simp [Ne.symm (rn .v31 (by decide))])
  have huc : u.v .v8=s.v .v8 := hu.get .v8 (by simp [Ne.symm (rn .v8 (by decide))])
  refine reduceTwo_ok (by decide) (Ne.symm hr24) (Ne.symm hq24) (Ne.symm hr25) (Ne.symm hq25) hrq hregs
    (by simpa only [huq] using hmod) (by simpa only [huc] using hc) fun v hv hva hvb => ?_
  have hk : VChg [.v27,.v29,.v24,.v25,r,q] s v := (hu.trans hv).mono (by
    paired_regs_sub)
  refine caddTwo_ok (by decide) (Ne.symm hr24) (Ne.symm hq24) (Ne.symm hr25) (Ne.symm hq25) hrq hregs
    (by intro e he; rw [hk.get .v31 (by simp [Ne.symm (rn .v31 (by decide)),Ne.symm (qn .v31 (by decide))])]; exact hmod e he)
    fun w hw hwa hwb => k w ((hk.trans hw).mono (by
      paired_regs_sub)) ?_ ?_
  · intro e he; rw [hwa e he,hva e he,ha e he]; rfl
  · intro e he; rw [hwb e he,hvb e he,hb e he]; rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowMls2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def lowMlsTwo (r q : VReg) : List Instr := mlsTwo r ++ reduceTwo .v24 .v25 r q

theorem lowMlsTwo_ok {r q : VReg} (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v,VChg [.v24,.v25,r,q] s v →
      (∀e<4,vword (v.v .v24) e=Response.reduceWord
        (vword (s.v .v24) e-vword (s.v .v26) e*vword (s.v .v15) e)) →
      (∀e<4,vword (v.v r) e=Response.reduceWord
        (vword (s.v r) e-vword (s.v .v28) e*vword (s.v .v15) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowMlsTwo r q++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  have hregs : ∀d∈[.v24,.v25,r,q],d≠.v8 ∧ d≠.v31 := by
    intro d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · decide
    · decide
    · exact ⟨rn .v8 (by decide),rn .v31 (by decide)⟩
    · exact ⟨qn .v8 (by decide),qn .v31 (by decide)⟩
  unfold lowMlsTwo
  rw [List.append_assoc]
  refine mlsTwo_ok (rn .v24 (by decide)) fun u hu ha hb => ?_
  refine reduceTwo_ok (by decide) (Ne.symm (rn .v24 (by decide))) (Ne.symm (qn .v24 (by decide)))
    (Ne.symm (rn .v25 (by decide))) (Ne.symm (qn .v25 (by decide))) hrq hregs
    (by intro e he; rw [hu.get .v31 (by simp [Ne.symm (rn .v31 (by decide))])]; exact hmod e he)
    (by intro e he; rw [hu.get .v8 (by simp [Ne.symm (rn .v8 (by decide))])]; exact hc e he)
    fun v hv hva hvb => k v ((hu.trans hv).mono (by
      paired_regs_sub)) ?_ ?_
  · intro e he; rw [hva e he,ha e he]
  · intro e he; rw [hvb e he,hb e he]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowTail2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def lowTailTwo (r q : VReg) (off : Nat) : List Instr :=
 storeTwo .v26 .v28 .x15 off ++ lowMlsTwo r q ++ storeTwo .v24 r .x16 off ++ normTwo r q

def lowPairWrites (s : State) (off : Nat) (ha hb la lb : BitVec 128) : Mem :=
 (((s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 ha).write
   (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16 hb).write
   (s.gpr .x16+BitVec.ofNat 64 off) 16 la).write
   (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16 lb

theorem lowPair_preserved {r q : VReg} (hr : r∉lowReserved) (hq : q∉lowReserved) :
    ∀d∈preservedV,d∉[.v24,.v25,r,q,.v30] := by
  have hp : ∀d∈preservedV,d∈lowReserved := by decide
  have ht : ∀d∈preservedV,d∉[.v24,.v25,.v30] := by decide
  intro d hd hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact ht .v24 hd (by simp)
  · exact ht .v25 hd (by simp)
  · exact hr (hp _ hd)
  · exact hq (hp _ hd)
  · exact ht .v30 hd (by simp)

theorem lowTailTwo_ok {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (wh0 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (wh1 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wl0 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (wl1 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v la lb,StepKeep [.v24,.v25,r,q,.v30] s v →
      v.mem=lowPairWrites s off (s.v .v26) (s.v .v28) la lb →
      (∀e<4,vword la e=Response.reduceWord
        (vword (s.v .v24) e-vword (s.v .v26) e*vword (s.v .v15) e)) →
      (∀e<4,vword lb e=Response.reduceWord
        (vword (s.v r) e-vword (s.v .v28) e*vword (s.v .v15) e)) →
      (∀e<4,vword (v.v .v30) e=
        (vword (s.v .v30) e ||| Response.normMask (vword la e) (vword (s.v .v9) e) (vword (s.v .v10) e)) |||
        Response.normMask (vword lb e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowTailTwo r q off++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  have hp := lowPair_preserved hr hq
  unfold lowTailTwo
  simp only [List.append_assoc]
  refine storeTwo_ok ho wh0 wh1 fun u hu huv hum => ?_
  refine lowMlsTwo_ok hr hq hrq (by simpa only [huv] using hmod)
    (by simpa only [huv] using hc) fun v hv hva hvb => ?_
  have hvkeep : StepKeep [.v24,.v25,r,q] u v := StepKeep.ofChg hv (by
    intro d hd hm; exact hp d hd (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
  have hk : StepKeep [.v24,.v25,r,q] s v := (hu.trans hvkeep).mono (by simp)
  refine storeTwo_ok ho
    (by rw [hk.keep.wr,hk.keep.get .x16]; exact wl0)
    (by rw [hk.keep.wr,hk.keep.get .x16]; exact wl1) fun w hw hwv hwm => ?_
  refine normTwo_ok (rn .v25 (by decide)) (qn .v25 (by decide))
    (qn .v10 (by decide)) (qn .v30 (by decide)) fun z hz hzf => ?_
  have hzkeep : StepKeep [.v25,q,.v30] w z := StepKeep.ofChg hz (by
    intro d hd hm; exact hp d hd (by simp only [List.mem_cons,List.not_mem_nil,or_false] at *; grind only))
  refine k z (v.v .v24) (v.v r) (((hk.trans hw).trans hzkeep).mono (by
    paired_regs_sub)) ?_ ?_ ?_ ?_
  · rw [hz.mem,hwm,hv.mem,hum,hk.keep.get .x16]
    rfl
  · simpa only [huv] using hva
  · simpa only [huv] using hvb
  · intro e he
    rw [hzf e he,hwv,
      hk.vec .v30 (by simp [Ne.symm (rn .v30 (by decide)),Ne.symm (qn .v30 (by decide))]),
      hk.vec .v9 (by simp [Ne.symm (rn .v9 (by decide)),Ne.symm (qn .v9 (by decide))]),
      hk.vec .v10 (by simp [Ne.symm (rn .v10 (by decide)),Ne.symm (qn .v10 (by decide))])]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPair` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

def lowPairClobs (r q : VReg) : List VReg := [.v27,.v29,.v24,.v25,r,q,.v26,.v28,.v30]

theorem lowPair_compose (g : Nat) (r q : VReg) (off : Nat) :
    lowPairBlocks g r q off=lowInputTwo r q off++lowHbTwo g r q++lowTailTwo r q off := by
  simp only [lowPairBlocks,lowInputTwo,lowHbTwo,lowTailTwo,lowMlsTwo,List.append_assoc]

theorem lowPair_ok {g : Nat} (hg : IsG g) {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (rd0 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (rd1 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wh0 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (wh1 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wl0 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (wl1 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v ha hb la lb,StepKeep (lowPairClobs r q) s v →
      v.mem=lowPairWrites s off ha hb la lb →
      (∀e<4,vword ha e=lowHighWord g (lowInputWord s r off e)) →
      (∀e<4,vword hb e=lowHighWord g (lowInputWord s q (off+128) e)) →
      (∀e<4,vword la e=Response.reduceWord
        (lowInputWord s r off e-lowHighWord g (lowInputWord s r off e)*vword (s.v .v15) e)) →
      (∀e<4,vword lb e=Response.reduceWord
        (lowInputWord s q (off+128) e-lowHighWord g (lowInputWord s q (off+128) e)*vword (s.v .v15) e)) →
      (∀e<4,vword (v.v .v30) e=
        (vword (s.v .v30) e ||| Response.normMask (vword la e) (vword (s.v .v9) e) (vword (s.v .v10) e)) |||
        Response.normMask (vword lb e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowPairBlocks g r q off++rest)) s Q := by
  have rn (d : VReg) (hd : d∈lowReserved) : r≠d := by intro he; exact hr (he ▸ hd)
  have qn (d : VReg) (hd : d∈lowReserved) : q≠d := by intro he; exact hq (he ▸ hd)
  rw [lowPair_compose]
  simp only [List.append_assoc]
  refine lowInputTwo_ok hr hq hrq ho rd0 rd1 hmod hc fun u hu hua hub => ?_
  have uk (d : VReg) (hd : d∈[.v11,.v12,.v13,.v14]) : u.v d=s.v d := by
    refine hu.get d ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · simp [Ne.symm (rn .v11 (by decide)),Ne.symm (qn .v11 (by decide))]
    · simp [Ne.symm (rn .v12 (by decide)),Ne.symm (qn .v12 (by decide))]
    · simp [Ne.symm (rn .v13 (by decide)),Ne.symm (qn .v13 (by decide))]
    · simp [Ne.symm (rn .v14 (by decide)),Ne.symm (qn .v14 (by decide))]
  refine lowHbTwo_ok hg (rn .v26 (by decide)) (qn .v25 (by decide))
    (qn .v26 (by decide)) (qn .v28 (by decide))
    (by simpa only [uk .v11 (by simp)] using h11)
    (by simpa only [uk .v12 (by simp)] using h12)
    (by simpa only [uk .v13 (by simp)] using h13)
    (by simpa only [uk .v14 (by simp)] using h14) fun v hv hva hvb => ?_
  have hk : VChg [.v27,.v29,.v24,.v25,r,q,.v26,.v28] s v := (hu.trans hv).mono (by
    paired_regs_sub)
  have vk (d : VReg) (hd : d∈[.v8,.v9,.v10,.v15,.v30,.v31]) : v.v d=s.v d := by
    refine hk.get d ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [Ne.symm (rn .v8 (by decide)),Ne.symm (qn .v8 (by decide))]
    · simp [Ne.symm (rn .v9 (by decide)),Ne.symm (qn .v9 (by decide))]
    · simp [Ne.symm (rn .v10 (by decide)),Ne.symm (qn .v10 (by decide))]
    · simp [Ne.symm (rn .v15 (by decide)),Ne.symm (qn .v15 (by decide))]
    · simp [Ne.symm (rn .v30 (by decide)),Ne.symm (qn .v30 (by decide))]
    · simp [Ne.symm (rn .v31 (by decide)),Ne.symm (qn .v31 (by decide))]
  have va (e : Nat) (he : e<4) : vword (v.v .v24) e=lowInputWord s r off e := by
    rw [hv.get .v24 (by simp [Ne.symm (qn .v24 (by decide))])]; exact hua e he
  have vb (e : Nat) (he : e<4) : vword (v.v r) e=lowInputWord s q (off+128) e := by
    rw [hv.get r (by simp [rn .v25 (by decide),hrq,rn .v26 (by decide),rn .v28 (by decide)])]; exact hub e he
  have higha (e : Nat) (he : e<4) : vword (v.v .v26) e=lowHighWord g (lowInputWord s r off e) := by rw [hva e he,hua e he]
  have highb (e : Nat) (he : e<4) : vword (v.v .v28) e=lowHighWord g (lowInputWord s q (off+128) e) := by rw [hvb e he,hub e he]
  have hp : ∀d∈preservedV,d∉[.v27,.v29,.v24,.v25,r,q,.v26,.v28] := by
    intro d hd hm
    have h1 := lowPair_preserved hr hq d hd
    have h2 := (by decide : ∀d∈preservedV,d∉[.v26,.v27,.v28,.v29]) d hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  have frame := hk.keep hp
  refine lowTailTwo_ok hr hq hrq ho
    (by rw [frame.wr,frame.get .x15]; exact wh0)
    (by rw [frame.wr,frame.get .x15]; exact wh1)
    (by rw [frame.wr,frame.get .x16]; exact wl0)
    (by rw [frame.wr,frame.get .x16]; exact wl1)
    (by simpa only [vk .v31 (by simp)] using hmod)
    (by simpa only [vk .v8 (by simp)] using hc) fun w la lb hw hm hla hlb hf =>
      k w (v.v .v26) (v.v .v28) la lb (((StepKeep.ofChg hk hp).trans hw).mono (by
        intro d hd; simp only [lowPairClobs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ higha highb ?_ ?_ ?_
  · rw [hm]
    simp only [lowPairWrites,hk.mem,hk.gpr]
  · intro e he; rw [hla e he,va e he,higha e he,vk .v15 (by simp)]
  · intro e he; rw [hlb e he,vb e he,highb e he,vk .v15 (by simp)]
  · intro e he; rw [hf e he,vk .v30 (by simp),vk .v9 (by simp),vk .v10 (by simp)]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowShape` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (vr)

/-- Every scheduled raw-register pair is distinct and outside the reserved constants/scratch. -/
theorem lowPair_registers {p j : Nat} (hp : p<2) (hj : j<4) :
    vr (8*p+2*j)∉lowReserved ∧ vr (8*p+2*j+1)∉lowReserved ∧
      vr (8*p+2*j)≠vr (8*p+2*j+1) := by
  have h : ∀p : Fin 2,∀j : Fin 4,
      vr (8*p.val+2*j.val)∉lowReserved ∧ vr (8*p.val+2*j.val+1)∉lowReserved ∧
      vr (8*p.val+2*j.val)≠vr (8*p.val+2*j.val+1) := by decide
  exact h ⟨p,hp⟩ ⟨j,hj⟩

/-- Both vectors remain in their bank's polynomial region. -/
theorem lowPair_offsets {p j : Nat} (hp : p<2) (hj : j<4) :
    (1024*p+256*j)%16=0 ∧ 1024*p+256*j+128<65536 ∧
      1024*p≤1024*p+256*j ∧ 1024*p+256*j+128+16≤1024*p+1024 := by
  constructor
  · omega_using []
  · omega_using [hp, hj]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowModel` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord normMask)

structure LowConstants where
  scale : BitVec 128
  lower : BitVec 128
  width : BitVec 128

def lowConstantsAt (s : State) : LowConstants := ⟨s.v .v15,s.v .v9,s.v .v10⟩

def lowInputValues (m : Mem) (addr : Addr) (raw : BitVec 128) (e : Nat) : BitVec 32 :=
 Inverse.signCorrected (reduceWord (vword (m.read addr 16) e-vword raw e))

/-- Both source vectors are read before the four writes, exactly as in the pipeline.
The model does not impose nonalias assumptions. -/
def lowPairStep (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) : CheckData :=
 let a := lowInputValues d.mem out0 raw0
 let b := lowInputValues d.mem out1 raw1
 let ha := fun e => lowHighWord g (a e)
 let hb := fun e => lowHighWord g (b e)
 let la := fun e => reduceWord (a e-ha e*vword c.scale e)
 let lb := fun e => reduceWord (b e-hb e*vword c.scale e)
 { mem := (((d.mem.write out0 16 (laneVector ha)).write out1 16 (laneVector hb)).write
     aux0 16 (laneVector la)).write aux1 16 (laneVector lb)
   flags := laneVector fun e =>
     (vword d.flags e ||| normMask (la e) (vword c.lower e) (vword c.width e)) |||
       normMask (lb e) (vword c.lower e) (vword c.width e)
   count := d.count }
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end


/-! ## `PairedLowStep` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep laneVector laneVector_word)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

theorem lowPairStep_ok {g : Nat} (hg : IsG g) {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (rd0 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (rd1 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wh0 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (wh1 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wl0 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (wl1 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v,StepKeep (lowPairClobs r q) s v →
      dataAt v=lowPairStep g (s.v r) (s.v q)
        (s.gpr .x15+BitVec.ofNat 64 off) (s.gpr .x15+BitVec.ofNat 64 (off+128))
        (s.gpr .x16+BitVec.ofNat 64 off) (s.gpr .x16+BitVec.ofNat 64 (off+128))
        (lowConstantsAt s) (dataAt s) → WP isa (.block rest) v Q) :
    WP isa (.block (lowPairBlocks g r q off++rest)) s Q := by
  refine lowPair_ok hg hr hq hrq ho rd0 rd1 wh0 wh1 wl0 wl1 hmod hc h11 h12 h13 h14
    fun v ha hb la lb hv hm hha hhb hla hlb hf => k v hv ?_
  have vecEq (v : BitVec 128) (f : Nat → BitVec 32)
      (h : ∀e<4,vword v e=f e) : v=laneVector f := by
    apply vec_ext
    intro e he
    rw [laneVector_word _ he]
    exact h e he
  have eha := vecEq ha _ hha
  have ehb := vecEq hb _ hhb
  have ela := vecEq la _ hla
  have elb := vecEq lb _ hlb
  rw [eha,ehb,ela,elb] at hm
  rw [ela,elb] at hf
  apply checkData_ext
  · simpa only [lowPairWrites,lowPairStep,lowInputValues,lowInputWord,lowConstantsAt,dataAt] using hm
  · apply vec_ext
    intro e he
    simpa only [lowPairStep,lowInputValues,lowInputWord,lowConstantsAt,dataAt,laneVector_word _ he] using hf e he
  · have rn : r≠.v14 := by intro he; exact hr (by simp [he,lowReserved])
    have qn : q≠.v14 := by intro he; exact hq (by simp [he,lowReserved])
    exact hv.vec .v14 (by simp [lowPairClobs,Ne.symm rn,Ne.symm qn])
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPending` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (vr)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

abbrev LowIndex := Fin 2 × Fin 4
def lowRaw0 (i : LowIndex) : VReg := vr (8*i.1.val+2*i.2.val)
def lowRaw1 (i : LowIndex) : VReg := vr (8*i.1.val+2*i.2.val+1)
def lowValue0 (v : Values) (i : LowIndex) : BitVec 128 := (v i.1)[2*i.2.val]
def lowValue1 (v : Values) (i : LowIndex) : BitVec 128 := (v i.1)[2*i.2.val+1]
def lowOff (i : LowIndex) : Nat := 1024*i.1.val+256*i.2.val

def LowPending (s : State) (v : Values) (is : List LowIndex) : Prop :=
  ∀i∈is,s.v (lowRaw0 i)=lowValue0 v i ∧ s.v (lowRaw1 i)=lowValue1 v i

theorem Banks.lowPending {s : State} {v : Values} (h : Banks s v) (is : List LowIndex) : LowPending s v is := by
  intro i hi
  constructor
  · simpa only [bankRegs,Vector.getElem_ofFn,lowRaw0,lowValue0] using h i.1 ⟨2*i.2.val,by omega_using []⟩
  · simpa only [bankRegs,Vector.getElem_ofFn,lowRaw1,lowValue1,Nat.add_assoc] using h i.1 ⟨2*i.2.val+1,by omega_using []⟩

theorem low_raw_keep (i j : LowIndex) (hne : i≠j) :
    lowRaw0 j∉lowPairClobs (lowRaw0 i) (lowRaw1 i) ∧
    lowRaw1 j∉lowPairClobs (lowRaw0 i) (lowRaw1 i) := by
  rcases i with ⟨p,i⟩
  rcases j with ⟨q,j⟩
  revert p i q j
  decide

theorem LowPending.next {s t : State} {v : Values} {i : LowIndex} {is : List LowIndex}
    (h : LowPending s v (i::is)) (hn : i∉is)
    (hf : StepKeep (lowPairClobs (lowRaw0 i) (lowRaw1 i)) s t) : LowPending t v is := by
  intro j hj
  have hne : i≠j := by intro he; exact hn (he ▸ hj)
  have hk := low_raw_keep i j hne
  rw [hf.vec _ hk.1,hf.vec _ hk.2]
  exact h j (List.mem_cons_of_mem _ hj)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowReady` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.Round VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def lowRunRegs : List VReg := stageRunRegs++[.v30]

structure LowReady (g : Nat) (s : State) : Prop where
  q : ∀e<4,vword (s.v .v31) e=8380417#32
  bias : ∀e<4,vword (s.v .v8) e=4194304#32
  c11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127
  c12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g)
  c13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g)
  c14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g)

theorem LowReady.frame {g : Nat} {s t : State} (h : LowReady g s)
    (hf : StepFrame lowRunRegs s t) : LowReady g t := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hf.vec .v31 (by decide)]; exact h.q
  · rw [hf.vec .v8 (by decide)]; exact h.bias
  · rw [hf.vec .v11 (by decide)]; exact h.c11
  · rw [hf.vec .v12 (by decide)]; exact h.c12
  · rw [hf.vec .v13 (by decide)]; exact h.c13
  · rw [hf.vec .v14 (by decide)]; exact h.c14

theorem lowConstantsAt_frame {s t : State} (hf : StepFrame lowRunRegs s t) : lowConstantsAt t=lowConstantsAt s := by
  unfold lowConstantsAt
  rw [hf.vec .v15 (by decide),hf.vec .v9 (by decide),hf.vec .v10 (by decide)]

theorem lowClobs_subset (i : LowIndex) : lowPairClobs (lowRaw0 i) (lowRaw1 i)⊆lowRunRegs := by
  rcases i with ⟨p,j⟩
  revert p j
  decide

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRun` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round

def lowRun (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) : List LowIndex → CheckData
  | [] => d
  | i::is => lowRun g v out aux c (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d) is

def lowRunCode (g : Nat) (is : List LowIndex) : List Instr :=
  is.flatMap fun i => lowPairBlocks g (lowRaw0 i) (lowRaw1 i) (lowOff i)

theorem lowRun_ok {g : Nat} (hg : IsG g) (is : List LowIndex) (hn : is.Nodup)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : LowPending s v is) (hc : LowReady g s)
    (hr : ∀i:LowIndex,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i+128)) 16)
    (k : ∀t,StepFrame lowRunRegs s t → dataAt t=lowRun g v (s.gpr .x15) (s.gpr .x16)
      (lowConstantsAt s) (dataAt s) is → WP isa (.block rest) t Q) :
    WP isa (.block (lowRunCode g is++rest)) s Q := by
  induction is generalizing s with
  | nil => exact k s ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ rfl
  | cons i is ih =>
    simp only [lowRunCode,List.flatMap_cons,List.append_assoc]
    have hh := lowPair_registers i.1.isLt i.2.isLt
    have ho := lowPair_offsets i.1.isLt i.2.isLt
    refine lowPairStep_ok hg hh.1 hh.2.1 hh.2.2 ⟨ho.1,ho.2.1⟩
      (hr i).1 (hr i).2.1 (hr i).2.2.1 (hr i).2.2.2.1 (hr i).2.2.2.2.1 (hr i).2.2.2.2.2
      hc.q hc.bias hc.c11 hc.c12 hc.c13 hc.c14 fun a ha hda => ?_
    have haf : StepFrame lowRunRegs s a := (StepFrame.ofKeep ha).mono (lowClobs_subset i)
    refine ih (List.nodup_cons.mp hn).2 (hv.next (List.nodup_cons.mp hn).1 ha) (hc.frame haf) ?_
      fun t ht hdt => ?_
    · simpa only [haf.rd,haf.wr,haf.gpr] using hr
    · refine k t ((haf.trans ht).mono (by simp)) ?_
      have hvi := hv i (by simp)
      simp only [lowRaw0,lowRaw1] at hvi
      rw [hdt,haf.gpr,lowConstantsAt_frame haf,hda,hvi.1,hvi.2]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFinal` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Round

def allLow : List LowIndex := (List.finRange 2).flatMap fun p => (List.finRange 4).map fun j => (p,j)
def finalLowCode (g : Nat) : List Instr := finalLoads++finalArithmetic++lowRunCode g allLow

def finalLowData (g : Nat) (s : State) : CheckData :=
  lowRun g (rawPairAt s) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt s) (dataAt s) allLow

theorem lowReady_arithmetic {g : Nat} {s t : State} (h : LowReady g s)
    (hf : VChg stageRunRegs s t) : LowReady g t :=
  h.frame ((StepFrame.ofChg hf).mono (by intro r hr; exact List.mem_append_left _ hr))

theorem lowConstantsAt_arithmetic {s t : State} (hf : VChg stageRunRegs s t) : lowConstantsAt t=lowConstantsAt s :=
  lowConstantsAt_frame ((StepFrame.ofChg hf).mono (by intro r hr; exact List.mem_append_left _ hr))

theorem finalLow_ok {g : Nat} (hg : IsG g) {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (ht : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382)) (hc : LowReady g s)
    (hw : ∀i:LowIndex,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i+128)) 16)
    (k : ∀t,StepFrame lowRunRegs s t → dataAt t=finalLowData g s →
      WP isa (.block rest) t Q) : WP isa (.block (finalLowCode g++rest)) s Q := by
  simp only [finalLowCode,List.append_assoc]
  refine finalLoadArithmetic_ok hr ht hs hc.q fun a ha va => ?_
  refine lowRun_ok hg allLow (by decide) (va.lowPending allLow) (lowReady_arithmetic hc ha) ?_ fun t hf hd => ?_
  · simpa only [ha.rd,ha.wr,ha.gpr] using hw
  · refine k t (((StepFrame.ofChg ha).trans hf).mono (by simp [lowRunRegs])) ?_
    unfold finalLowData rawPairAt
    simpa only [ha.gpr,lowConstantsAt_arithmetic ha,dataAt_arithmetic ha] using hd

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPartition` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired (r0Pair finalPaired)

theorem allLow_flatMap (f : Nat → Nat → List Instr) :
    [0,1].flatMap (fun p => (List.range 4).flatMap (fun j => f p j))=
      allLow.flatMap (fun i => f i.1.val i.2.val) := by
  have he : ([0,1].flatMap fun p => (List.range 4).map fun j => (p,j))=
      allLow.map (fun i => (i.1.val,i.2.val)) := by decide
  have h := congrArg (fun xs : List (Nat × Nat) => xs.flatMap (fun i => f i.1 i.2)) he
  simpa only [List.flatMap_assoc,List.flatMap_map] using h

theorem lowRunCode_eq (g : Nat) :
    [0,1].flatMap (fun p => (List.range 4).flatMap (fun j => r0Pair g p j))=lowRunCode g allLow := by
  rw [allLow_flatMap]
  simp only [r0Pair_blocks,lowRunCode,lowRaw0,lowRaw1,lowOff]

theorem final_r0_eq (g : Nat) : finalPaired g=finalLowCode g++finalAdvance := by
  unfold finalPaired finalLowCode
  rw [finalPrefix_eq,lowRunCode_eq]
  simp only [List.append_assoc]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowMemory` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowRun_frame (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) {W : List Region} {ro ra : Region} {m : Mem}
    (ho : ro∈W) (ha : ra∈W)
    (hco : ∀i:LowIndex,ro.Contains (out+BitVec.ofNat 64 (lowOff i)) 16 ∧
      ro.Contains (out+BitVec.ofNat 64 (lowOff i+128)) 16)
    (hca : ∀i:LowIndex,ra.Contains (aux+BitVec.ofNat 64 (lowOff i)) 16 ∧
      ra.Contains (aux+BitVec.ofNat 64 (lowOff i+128)) 16)
    (hf : Frame W m d.mem) : Frame W m (lowRun g v out aux c d is).mem := by
  induction is generalizing d with
  | nil => exact hf
  | cons i is ih =>
    simp only [lowRun]
    exact ih _ ((((hf.write ho _ (hco i).1).write ho _ (hco i).2).write ha _ (hca i).1).write ha _ (hca i).2)

def lowPassData (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) : Nat → CheckData
  | 0 => d
  | u+1 =>
    let prev := lowPassData g work out aux c d u
    let v := fun p => Inverse.rawFinalValues (readPair prev.mem (work+BitVec.ofNat 64 (16*u)) 128 p)
    lowRun g v (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c prev allLow

theorem lowPass_frame (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u : Nat} (hu : u≤8) :
    Frame [⟨out,2048⟩,⟨aux,2048⟩] d.mem (lowPassData g work out aux c d u).mem := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [lowPassData]
    refine lowRun_frame _ _ _ _ _ _ _ (ro:=⟨out,2048⟩) (ra:=⟨aux,2048⟩)
      (by simp) (by simp) ?_ ?_ (ih (by omega_using [hu]))
    · intro i
      constructor <;> rw [BitVec.add_assoc,← BitVec.ofNat_add] <;>
        exact Offset.contains_base out (by dsimp only [lowOff]; omega_using [hu]) (by dsimp only [lowOff]; omega_using [hu])
    · intro i
      constructor <;> rw [BitVec.add_assoc,← BitVec.ofNat_add] <;>
        exact Offset.contains_base aux (by dsimp only [lowOff]; omega_using [hu]) (by dsimp only [lowOff]; omega_using [hu])

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRead` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowPair_read_other (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (a : Addr)
    (h0 : Mem.Sep a 16 out0 16) (h1 : Mem.Sep a 16 out1 16)
    (h2 : Mem.Sep a 16 aux0 16) (h3 : Mem.Sep a 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read a 16=d.mem.read a 16 := by
  simp only [lowPairStep]
  rw [Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide),
    Mem.read_write_sep h1 (by decide),Mem.read_write_sep h0 (by decide)]

theorem lowRun_read_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (a : Addr)
    (hs : ∀i∈is,Mem.Sep a 16 (out+BitVec.ofNat 64 (lowOff i)) 16 ∧
      Mem.Sep a 16 (out+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      Mem.Sep a 16 (aux+BitVec.ofNat 64 (lowOff i)) 16 ∧
      Mem.Sep a 16 (aux+BitVec.ofNat 64 (lowOff i+128)) 16) :
    (lowRun g v out aux c d is).mem.read a 16=d.mem.read a 16 := by
  induction is generalizing d with
  | nil => rfl
  | cons i is ih =>
    rw [lowRun,ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj))]
    have h := hs i (by simp)
    exact lowPair_read_other _ _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowWriteValues` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord)

private theorem read128_write_self (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.write a 16 v).read a 16=v := by
  simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m a 16 v (by decide)

def lowHighOutput (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) : BitVec 128 :=
  laneVector fun e => lowHighWord g (lowInputValues m out raw e)

def lowLowOutput (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) (c : LowConstants) : BitVec 128 :=
  laneVector fun e => reduceWord (lowInputValues m out raw e-
    lowHighWord g (lowInputValues m out raw e)*vword c.scale e)

theorem lowPair_mem (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem=
      (((d.mem.write out0 16 (lowHighOutput g d.mem out0 raw0)).write out1 16
        (lowHighOutput g d.mem out1 raw1)).write aux0 16
        (lowLowOutput g d.mem out0 raw0 c)).write aux1 16 (lowLowOutput g d.mem out1 raw1 c) := rfl

/-- The first high output survives all three subsequent stores. -/
theorem lowPair_read_high0 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData)
    (h1 : Mem.Sep out0 16 out1 16) (h2 : Mem.Sep out0 16 aux0 16) (h3 : Mem.Sep out0 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read out0 16=lowHighOutput g d.mem out0 raw0 := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide),
    Mem.read_write_sep h1 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_high1 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData)
    (h2 : Mem.Sep out1 16 aux0 16) (h3 : Mem.Sep out1 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read out1 16=lowHighOutput g d.mem out1 raw1 := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_low0 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (h3 : Mem.Sep aux0 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read aux0 16=lowLowOutput g d.mem out0 raw0 c := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_low1 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read aux1 16=lowLowOutput g d.mem out1 raw1 c := by
  rw [lowPair_mem]
  exact read128_write_self _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFlagValue` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def lowMask (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) (c : LowConstants) (e : Nat) : BitVec 32 :=
  normMask (reduceWord (lowInputValues m out raw e-
    lowHighWord g (lowInputValues m out raw e)*vword c.scale e)) (vword c.lower e) (vword c.width e)

/-- Both paired coefficient checks contribute to the rejection accumulator. -/
theorem lowPair_flag (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags e=
      (vword d.flags e ||| lowMask g d.mem out0 raw0 c e) ||| lowMask g d.mem out1 raw1 c e := by
  simp only [lowPairStep,lowMask,laneVector_word _ he]

theorem lowPair_flag_zero (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags e=0 ↔
      (vword d.flags e=0 ∧ lowMask g d.mem out0 raw0 c e=0) ∧ lowMask g d.mem out1 raw1 c e=0 := by
  rw [lowPair_flag _ _ _ _ _ _ _ _ _ he]
  exact BitVec.or_eq_zero_iff.trans (and_congr_left fun _ => BitVec.or_eq_zero_iff)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowSlotLayout` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowAddr (base : Addr) (i : LowIndex) (half : Fin 2) : Addr :=
  base+BitVec.ofNat 64 (lowOff i+128*half.val)

theorem lowAddr_sep (base : Addr) {i j : LowIndex} {h k : Fin 2}
    (hne : i≠j ∨ h≠k) : Mem.Sep (lowAddr base i h) 16 (lowAddr base j k) 16 := by
  have hi : i.1.val≠j.1.val ∨ i.2.val≠j.2.val ∨ h.val≠k.val := by
    by_contra hn
    simp only [not_or,not_not] at hn
    have he : i=j := Prod.ext (Fin.ext hn.1) (Fin.ext hn.2.1)
    have hh : h=k := Fin.ext hn.2.2
    rcases hne with hn | hn
    · exact hn he
    · exact hn hh
  simp only [lowAddr,lowOff]
  exact Offset.sep base (by omega_using [hi]) (by omega_using []) (by omega_using [])

theorem lowAddr_contains (base : Addr) {u : Nat} (hu : u<8) (i : LowIndex) (h : Fin 2) :
    (⟨base,2048⟩ : Region).Contains (lowAddr (base+BitVec.ofNat 64 (16*u)) i h) 16 := by
  simp only [lowAddr,lowOff,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.contains_base base (by omega_using [hu]) (by omega_using [hu])

/-- Disjoint later paired checks preserve either half of either output. -/
theorem lowRun_read_slot_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hn : i∉is) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr out i h) 16=d.mem.read (lowAddr out i h) 16 := by
  apply lowRun_read_other
  intro j hj
  have hnij : i≠j := by intro he; subst j; exact hn hj
  have ho0 := lowAddr_sep (h:=h) (k:=0) out (Or.inl hnij)
  have ho1 := lowAddr_sep (h:=h) (k:=1) out (Or.inl hnij)
  have contain (base : Addr) (i : LowIndex) (h : Fin 2) :
      (⟨base,2048⟩ : Region).Contains (lowAddr base i h) 16 := by
    simp only [lowAddr,lowOff]
    exact Offset.contains_base base (by omega_using []) (by omega_using [])
  have ha0 := hd.sep (contain out i h) (contain aux j 0)
  have ha1 := hd.sep (contain out i h) (contain aux j 1)
  simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
    And.intro ho0 (And.intro ho1 (And.intro ha0 ha1))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowInputFrame` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowAddr_contains_base (base : Addr) (i : LowIndex) (h : Fin 2) :
    (⟨base,2048⟩ : Region).Contains (lowAddr base i h) 16 := by
  simp only [lowAddr,lowOff]
  exact Offset.contains_base base (by omega_using []) (by omega_using [])

/-- Both original input vectors of a later pair survive this pair's four stores. -/
theorem lowPair_other_input (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) {i j : LowIndex} (hne : j≠i) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr out j h) 16=d.mem.read (lowAddr out j h) 16 := by
  apply lowPair_read_other
  · simpa only [lowAddr,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using
      lowAddr_sep (h:=h) (k:=0) out (Or.inl hne)
  · simpa only [lowAddr,Fin.val_one,Nat.mul_one] using
      lowAddr_sep (h:=h) (k:=1) out (Or.inl hne)
  · simpa only [lowAddr,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using
      hd.sep (lowAddr_contains_base out j h) (lowAddr_contains_base aux i 0)
  · simpa only [lowAddr,Fin.val_one,Nat.mul_one] using
      hd.sep (lowAddr_contains_base out j h) (lowAddr_contains_base aux i 1)

theorem lowMask_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128)
    (c : LowConstants) (e : Nat) (hm : m'.read out 16=m.read out 16) :
    lowMask g m' out raw c e=lowMask g m out raw c e := by
  simp only [lowMask,lowInputValues,hm]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowHalfOutput` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowHalfValue (v : Values) (i : LowIndex) (h : Fin 2) : BitVec 128 :=
  (v i.1)[2*i.2.val+h.val]

/-- Each half of a paired step writes its exact high result. -/
theorem lowPair_read_high (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr out i h) 16=lowHighOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) := by
  have hd0 (h : Fin 2) := hd.sep (lowAddr_contains_base out i h) (lowAddr_contains_base aux i 0)
  have hd1 (h : Fin 2) := hd.sep (lowAddr_contains_base out i h) (lowAddr_contains_base aux i 1)
  fin_cases h
  · exact lowPair_read_high0 _ _ _ _ _ _ _ _ _
      (lowAddr_sep out (h:=0) (k:=1) (Or.inr (by decide))) (hd0 0) (hd1 0)
  · exact lowPair_read_high1 _ _ _ _ _ _ _ _ _ (hd0 1) (hd1 1)

/-- Each half also writes its exact signed low result, including rejected paths. -/
theorem lowPair_read_low (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (i : LowIndex) (h : Fin 2) :
    (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem.read
      (lowAddr aux i h) 16=lowLowOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) c := by
  fin_cases h
  · exact lowPair_read_low0 _ _ _ _ _ _ _ _ _ (lowAddr_sep aux (h:=0) (k:=1) (Or.inr (by decide)))
  · exact lowPair_read_low1 _ _ _ _ _ _ _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPassRead` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowSlice_sep (base : Addr) {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u)
    (i j : LowIndex) (h t : Fin 2) :
    Mem.Sep (lowAddr (base+BitVec.ofNat 64 (16*k)) i h) 16
      (lowAddr (base+BitVec.ofNat 64 (16*u)) j t) 16 := by
  simp only [lowAddr,lowOff,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep base (by omega_using [hu, hk, hne]) (by omega_using [hk]) (by omega_using [hu])

/-- Earlier r0 iterations preserve both inputs of every later pair. -/
theorem lowPass_read_future (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u k : Nat} (hu : u≤k) (hk : k<8) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d u).mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16=
      d.mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16 := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_,ih (by omega_using [hu])]
    intro j _
    have h0 := lowSlice_sep out (by omega_using [hk, hu] : u<8) hk (by omega_using [hu] : k≠u) i j h 0
    have h1 := lowSlice_sep out (by omega_using [hk, hu] : u<8) hk (by omega_using [hu] : k≠u) i j h 1
    have h2 := hd.sep (lowAddr_contains out hk i h) (lowAddr_contains aux (by omega_using [hk, hu] : u<8) j 0)
    have h3 := hd.sep (lowAddr_contains out hk i h) (lowAddr_contains aux (by omega_using [hk, hu] : u<8) j 1)
    simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
      And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRunFlags` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def lowPairAccept (g : Nat) (v : Values) (out : Addr) (c : LowConstants) (m : Mem)
    (e : Nat) (i : LowIndex) : Prop :=
  lowMask g m (out+BitVec.ofNat 64 (lowOff i)) (lowValue0 v i) c e=0 ∧
  lowMask g m (out+BitVec.ofNat 64 (lowOff i+128)) (lowValue1 v i) c e=0

/-- A paired r0 sequence accepts precisely all its original-input norm checks. -/
theorem lowRun_flag_zero_iff (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (hn : is.Nodup)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) {e : Nat} (he : e<4) :
    vword (lowRun g v out aux c d is).flags e=0 ↔
      vword d.flags e=0 ∧ ∀i∈is,lowPairAccept g v out c d.mem e i := by
  induction is generalizing d with
  | nil => simp only [lowRun,List.not_mem_nil,false_implies,implies_true,and_true]
  | cons i is ih =>
    have hn' := List.nodup_cons.mp hn
    rw [lowRun,ih _ hn'.2,lowPair_flag_zero _ _ _ _ _ _ _ _ _ he]
    have ht : (∀j∈is,lowPairAccept g v out c
        (lowPairStep g (lowValue0 v i) (lowValue1 v i)
          (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
          (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem e j) ↔
        ∀j∈is,lowPairAccept g v out c d.mem e j := by
      have hp (j : LowIndex) (hj : j∈is) : lowPairAccept g v out c
          (lowPairStep g (lowValue0 v i) (lowValue1 v i)
            (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
            (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d).mem e j ↔
          lowPairAccept g v out c d.mem e j := by
        have hnij : j≠i := by intro h; subst j; exact hn'.1 hj
        have h0 := lowPair_other_input g v out aux c d hnij 0 hd
        have h1 := lowPair_other_input g v out aux c d hnij 1 hd
        simp only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at h0 h1
        unfold lowPairAccept
        rw [lowMask_read_eq _ _ _ _ _ h0,lowMask_read_eq _ _ _ _ _ h1]
      exact ⟨fun h j hj => (hp j hj).mp (h j hj),fun h j hj => (hp j hj).mpr (h j hj)⟩
    rw [ht]
    simp only [List.mem_cons,forall_eq_or_imp,lowPairAccept,and_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
