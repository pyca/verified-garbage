import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLane
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckModel

/-! ## `PairedLowHf2` -/

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
  refine wp_strq (by omega) rfl hr fun u hu =>
    wp_strq (by omega) rfl (by rw [hu.wr,hu.gpr]; exact hr') fun v hv =>
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
  by_cases hg : g==261888
  · simp only [hg,ite_true]
    rfl
  · simp only [hg]
    rfl
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
    intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
  refine caddTwo_ok (by decide) (Ne.symm hr24) (Ne.symm hq24) (Ne.symm hr25) (Ne.symm hq25) hrq hregs
    (by intro e he; rw [hk.get .v31 (by simp [Ne.symm (rn .v31 (by decide)),Ne.symm (qn .v31 (by decide))])]; exact hmod e he)
    fun w hw hwa hwb => k w ((hk.trans hw).mono (by
      intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_
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
      intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_
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
    intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_ ?_ ?_ ?_
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
    intro d hd; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)
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
  · omega
  · omega
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
