module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackBlock
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `MlDsa.AArch64.Optimized.UseHintPackLoop`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.UseHintPackLoad`, which only this module used -/

section

/-! ## From `UseHintPackVec.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

 theorem csub_ok {s : State} {rest : List Instr} {Q : State→Prop}
    (k : ∀t,VChg [.v6,.v7] s t →
      (∀e<4,vword (t.v .v6) e=csub (vword (s.v .v20) e) (vword (s.v .v6) e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.UseHintPack.csub .v6 .v20++rest)) s Q := by
  refine wp_vop (d:=.v7) rfl fun a ha=>wp_vop (d:=.v6) rfl fun t ht=>?_
  refine k t ((ha.chg.trans ht.chg).mono (by decide)) ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v6,ha.v,VG.AArch64.vword_map2 _ _ _ he]
  rfl

 def adjustCode : List Instr :=
  [.vop (.mul .v26 .v6 .v21),.vop (.sub .s4 .v26 .v26 .v4),
   .vop (.shift .ushr .s4 .v26 .v26 31),.vop (.shift .shl .s4 .v26 .v26 1),
   .vop (.sub .s4 .v26 .v26 .v22),.vop (.cmeq .s4 .v5 .v5 .v23),
   .vop (.logic .bic .v26 .v26 .v5),.vop (.add .s4 .v6 .v6 .v26),
   .vop (.add .s4 .v6 .v6 .v20)]

 theorem adjust_ok {s : State} {rest : List Instr} {Q : State→Prop}
    (hzero : ∀e<4,vword (s.v .v23) e=0) (hone : ∀e<4,vword (s.v .v22) e=1)
    (k : ∀t,VChg [.v5,.v6,.v26] s t →
      (∀e<4,vword (t.v .v6) e=
        vword (s.v .v6) e+
        (if vword (s.v .v5) e=0 then (0 : BitVec 32) else
          (((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1)+
        vword (s.v .v20) e) → WP isa (.block rest) t Q) :
    WP isa (.block (adjustCode++rest)) s Q := by
  refine wp_vop (d:=.v26) rfl fun s1 h1=>wp_vop (d:=.v26) rfl fun s2 h2=>
    wp_vop (d:=.v26) rfl fun s3 h3=>wp_vop (d:=.v26) rfl fun s4 h4=>
    wp_vop (d:=.v26) rfl fun s5 h5=>wp_vop (d:=.v5) rfl fun s6 h6=>
    wp_vop (d:=.v26) rfl fun s7 h7=>wp_vop (d:=.v6) rfl fun s8 h8=>
    wp_vop (d:=.v6) rfl fun t h9=>?_
  have hk := (((((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg).trans h7.chg).trans h8.chg).trans h9.chg
  refine k t (hk.mono (by decide)) ?_
  intro e he
  have e1 : vword (s1.v .v26) e=vword (s.v .v6) e*vword (s.v .v21) e := by
    rw [h1.v,VG.AArch64.vword_map2 _ _ _ he]
  have e2 : vword (s2.v .v26) e=vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e := by
    rw [h2.v,VG.AArch64.vword_map2 _ _ _ he,e1,h1.get .v4]
  have e3 : vword (s3.v .v26) e=(vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31 := by
    rw [h3.v,VG.AArch64.vword_map2 _ _ _ he,e2]; rfl
  have e4 : vword (s4.v .v26) e=((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1 := by
    rw [h4.v,VG.AArch64.vword_map2 _ _ _ he,e3]; rfl
  have e5 : vword (s5.v .v26) e=(((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1 := by
    rw [h5.v,VG.AArch64.vword_map2 _ _ _ he,e4,h4.get .v22,h3.get .v22,h2.get .v22,h1.get .v22,hone e he]
  have e6 : vword (s6.v .v5) e=if vword (s.v .v5) e=0 then (-1 : BitVec 32) else 0 := by
    rw [h6.v,VG.AArch64.vword_map2 _ _ _ he,
      h5.get .v5,h4.get .v5,h3.get .v5,h2.get .v5,h1.get .v5,
      h5.get .v23,h4.get .v23,h3.get .v23,h2.get .v23,h1.get .v23,hzero e he]
    rfl
  have e7 : vword (s7.v .v26) e=if vword (s.v .v5) e=0 then (0 : BitVec 32) else
      (((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1 := by
    rw [h7.v]
    change vword (s6.v .v26 &&& ~~~s6.v .v5) e=_
    have hand (a b : BitVec 128) : vword (a &&& b) e=vword a e &&& vword b e := by
      simp only [vword,BitVec.extractLsb'_and]
    rw [hand,Response.word_not _ he]
    rw [h6.get .v26,e5,e6]
    split
    · simp
    · exact BitVec.and_allOnes
  have e8 : vword (s8.v .v6) e=vword (s.v .v6) e+
      (if vword (s.v .v5) e=0 then (0 : BitVec 32) else
        (((vword (s.v .v6) e*vword (s.v .v21) e-vword (s.v .v4) e) >>> 31) <<< 1)-1) := by
    rw [h8.v,VG.AArch64.vword_map2 _ _ _ he,e7,
      h7.get .v6,h6.get .v6,h5.get .v6,h4.get .v6,h3.get .v6,h2.get .v6,h1.get .v6]
  rw [h9.v,VG.AArch64.vword_map2 _ _ _ he,e8,
    h8.get .v20,h7.get .v20,h6.get .v20,h5.get .v20,h4.get .v20,h3.get .v20,h2.get .v20,h1.get .v20]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

structure Ready (g : Nat) (s : State) : Prop extends HighPack.PackReady g s where
  factor : ∀e<4,vword (s.v .v21) e=BitVec.ofNat 32 (2*g)
  one : ∀e<4,vword (s.v .v22) e=1
  z : ∀e<4,vword (s.v .v23) e=0

 theorem four_ok {g : Nat} (hg : IsG g) {r : VReg}
    (_hr : r∈([.v0,.v1,.v2,.v3] : List VReg)) {off : Nat} {s : State}
    (hc : Ready g s) (ho : off%16=0 ∧ off<4096*16)
    (ha : InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 off) 16)
    (hh : InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 off) 16)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,VChg [r,.v4,.v5,.v6,.v7,.v26] s t →
      (∀e<4,vword (t.v r) e=value g
        (vword (s.mem.read (s.gpr .x5+BitVec.ofNat 64 off) 16) e)
        (vword (s.mem.read (s.gpr .x4+BitVec.ofNat 64 off) 16) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g r off++rest)) s Q := by
  change WP isa (.block (.ldrq .v4 .x5 off :: .ldrq .v5 .x4 off ::
    (Impl.MlDsa.AArch64.Optimized.HighPack.hf g .v6 .v4 ++ (adjustCode ++
      (Impl.MlDsa.AArch64.Optimized.UseHintPack.csub .v6 .v20 ++
        (Impl.MlDsa.AArch64.Optimized.UseHintPack.csub .v6 .v20 ++ (.vop (.mov r .v6)::rest))))))) s Q
  refine wp_ldrq ho rfl ha fun a h1=>wp_ldrq ho rfl
    (by rw [h1.rd,h1.wr,h1.gpr]; exact hh) fun b h2=>?_
  have cb : HighPack.HighConstants g b := hc.toHighConstants.chg (h1.chg.trans h2.chg)
    (by decide) (by decide) (by decide) (by decide)
  refine HighPack.hf_ok hg (by decide) (by decide) cb.add cb.mul cb.round fun c h3 hraw=>?_
  have keep3 := (h1.chg.trans h2.chg).trans h3
  refine adjust_ok
    (fun e he=>by rw [keep3.get .v23 (by decide)]; exact hc.z e he)
    (fun e he=>by rw [keep3.get .v22 (by decide)]; exact hc.one e he) fun d h4 hadj=>?_
  have keep4 := keep3.trans h4
  have vpre : ∀e<4,vword (d.v .v6) e=before g
      (vword (s.mem.read (s.gpr .x5+BitVec.ofNat 64 off) 16) e)
      (vword (s.mem.read (s.gpr .x4+BitVec.ofNat 64 off) 16) e) := by
    intro e he
    rw [hadj e he,hraw e he,h2.get .v4,h1.v,
      keep3.get .v21 (by decide),hc.factor e he,keep3.get .v20 (by decide),hc.modulus e he,
      h3.get .v4 (by decide),h2.get .v4,h1.v,h3.get .v5 (by decide),h2.v,h1.mem,h1.gpr]
    rfl
  refine csub_ok fun f h5 hv5=>csub_ok fun u h6 hv6=>wp_vop (d:=r) rfl fun t h7=>?_
  have keep := ((keep4.trans h5).trans h6).trans h7.chg
  refine k t (keep.mono ?_) ?_
  · intro x hx
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind only
  · intro e he
    rw [h7.v]
    change vword (u.v .v6) e=_
    rw [hv6 e he,hv5 e he,vpre e he,h5.get .v20 (by decide),keep4.get .v20 (by decide),hc.modulus e he]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end

end

/-! ### `MlDsa.AArch64.Optimized.UseHintPackEncode`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open HighPack

/-- The vector packing tail depends only on the bounded fields supplied in
its lanes, so it also applies after UseHint. -/
theorem packedVector_fields {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (L : Vector Nat 256) (hbound : ∀i (hi : i<256),L[i]'hi<2^packWidth g)
    {s : State} (hc : PackConstants s) {block i : Nat}
    (hb : block<16) (hi : i<2*packWidth g)
    (hv : ∀j (hj : j<4),∀e (he : e<4),(vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e).toNat=
      L[16*block+4*j+e]'(by omega_using [hb, hj, he])) :
    vbyte (packedVector (packWidth g) s) i=
      (simpleBitPack L ((q-1)/(2*g)-1))[2*packWidth g*block+i]! := by
  have gathered : ∀j<16,vbyte (HighPack.gathered s) j=
      BitVec.ofNat 8 (L.toList.getD (16*block+j) 0) := by
    intro j hj
    rw [gathered_word s hj]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth,BitVec.toNat_ofNat,hv (j/4) (by omega_using [hj]) (j%4) (by omega_using [])]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp; omega_using [hb, hj]),Option.getD_some]
    simp only [Vector.getElem_toList]
    congr 2
    omega_using []
  have hlen : L.toList.length=256 := by simp
  have bounds : ∀a∈L.toList,a<2^packWidth g := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    exact hbound j (by simpa using hj)
  have hw : bitlen ((q-1)/(2*g)-1)=packWidth g := by rcases hg with rfl|rfl <;> rfl
  rw [simpleBitPack_eq,hw]
  rcases hg with rfl|rfl
  · exact encode4_byte hlen bounds hb hi gathered
  · exact encode6_byte hlen bounds hb hi hc gathered

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end

/-! ## From `UseHintPackFour.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/UseHintPackFields.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open HighPack

def fields (g : Nat) (m : Mem) (h a : Addr) : Vector Nat 256 :=
  Vector.ofFn fun i=>(value g (coeffAt m a i.val) (coeffAt m h i.val)).toNat

def packed (g : Nat) (m : Mem) (h a : Addr) : List Byte :=
  simpleBitPack (fields g m h a) ((q-1)/(2*g)-1)

 theorem fields_bound {g : Nat} (hg : IsG g) {m : Mem} {h a : Addr} (ha : Reduced m a)
    (i : Nat) (hi : i<256) : (fields g m h a)[i]'hi<2^packWidth g := by
  simp only [fields,Vector.getElem_ofFn]
  have hv := value_lt hg (h:=coeffAt m h i) (ha i hi)
  have hm : hbM g≤2^packWidth g := by rcases hg with rfl|rfl <;> decide
  exact Nat.lt_of_lt_of_le hv hm

 theorem packed_fields_byte {g : Nat} (hg : IsG g) {s : State} {m : Mem} {h a : Addr}
    (ha : Reduced m a) (hc : PackConstants s) {block i : Nat} (hb : block<16)
    (hi : i<2*packWidth g)
    (hv : ∀j<4,∀e<4,vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=value g
      (vword (m.read ((a+BitVec.ofNat 64 (64*block))+BitVec.ofNat 64 (16*j)) 16) e)
      (vword (m.read ((h+BitVec.ofNat 64 (64*block))+BitVec.ofNat 64 (16*j)) 16) e)) :
    vbyte (packedVector (packWidth g) s) i=(packed g m h a)[2*packWidth g*block+i]! := by
  apply packedVector_fields hg (fields g m h a) (fields_bound hg ha) hc hb hi
  intro j hj e he
  rw [hv j hj e he,VG.AArch64.vword_read16 _ _ he,VG.AArch64.vword_read16 _ _ he,
    Offset.add_add,Offset.add_add,Offset.add_add,Offset.add_add]
  simp only [fields,Vector.getElem_ofFn,coeffAt]
  rw [show 64*block+(16*j+4*e)=4*(16*block+4*j+e) by omega_using []]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (VChg)

def temps : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v26]

 theorem Ready.chg {g : Nat} {s t : State} (h : Ready g s) {rs : List VReg}
    (k : VChg rs s t) (hrs : rs⊆temps) : Ready g t := by
  have hk := k.mono hrs
  refine ⟨⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩,?_,?_,?_⟩
  · intro e he; rw [hk.get .v17 (by decide)]; exact h.add e he
  · intro e he; rw [hk.get .v18 (by decide)]; exact h.mul e he
  · intro e he; rw [hk.get .v19 (by decide)]; exact h.round e he
  · intro e he; rw [hk.get .v20 (by decide)]; exact h.modulus e he
  · rw [hk.get .v28 (by decide)]; exact h.zero
  · rw [hk.get .v29 (by decide)]; exact h.idx29
  · rw [hk.get .v24 (by decide)]; exact h.idx24
  · rw [hk.get .v25 (by decide)]; exact h.idx25
  · intro e he; rw [hk.get .v21 (by decide)]; exact h.factor e he
  · intro e he; rw [hk.get .v22 (by decide)]; exact h.one e he
  · intro e he; rw [hk.get .v23 (by decide)]; exact h.z e he

 def loadFour (g : Nat) : List Instr :=
  ([.v0,.v1,.v2,.v3] : List VReg).zipIdx.flatMap fun (r,j)=>
    Impl.MlDsa.AArch64.Optimized.UseHintPack.four g r (16*j)

 theorem loadFour_ok {g : Nat} (hg : IsG g) {s : State} (hc : Ready g s)
    (ha : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hh : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,VChg temps s t → Ready g t →
      (∀j<4,∀e<4,vword (t.v ([.v0,.v1,.v2,.v3] : List VReg)[j]!) e=value g
        (vword (s.mem.read (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16) e)
        (vword (s.mem.read (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (loadFour g++rest)) s Q := by
  change WP isa (.block (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v0 0 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v1 16 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v2 32 ++
    (Impl.MlDsa.AArch64.Optimized.UseHintPack.four g .v3 48 ++ rest))))) s Q
  refine four_ok hg (by decide) hc (by decide) (ha 0 (by decide)) (hh 0 (by decide)) fun a h0 w0=>?_
  have c0 := hc.chg h0 (by decide)
  refine four_ok hg (by decide) c0 (by decide)
    (by rw [h0.rd,h0.wr,h0.gpr]; exact ha 1 (by decide))
    (by rw [h0.rd,h0.wr,h0.gpr]; exact hh 1 (by decide)) fun b h1 w1=>?_
  have k1 := h0.trans h1
  have c1 := c0.chg h1 (by decide)
  refine four_ok hg (by decide) c1 (by decide)
    (by rw [k1.rd,k1.wr,k1.gpr]; exact ha 2 (by decide))
    (by rw [k1.rd,k1.wr,k1.gpr]; exact hh 2 (by decide)) fun c h2 w2=>?_
  have k2 := k1.trans h2
  have c2 := c1.chg h2 (by decide)
  refine four_ok hg (by decide) c2 (by decide)
    (by rw [k2.rd,k2.wr,k2.gpr]; exact ha 3 (by decide))
    (by rw [k2.rd,k2.wr,k2.gpr]; exact hh 3 (by decide)) fun t h3 w3=>?_
  refine k t ((k2.trans h3).mono (by decide)) (c2.chg h3 (by decide)) ?_
  intro j hj e he
  rcases (show j=0∨j=1∨j=2∨j=3 by omega_arith) with rfl|rfl|rfl|rfl
  · change vword (t.v .v0) e=_
    rw [h3.get .v0 (by decide),h2.get .v0 (by decide),h1.get .v0 (by decide),w0 e he]
  · change vword (t.v .v1) e=_
    rw [h3.get .v1 (by decide),h2.get .v1 (by decide),w1 e he,h0.mem,h0.gpr]
  · change vword (t.v .v2) e=_
    rw [h3.get .v2 (by decide),w2 e he,k1.mem,k1.gpr]
  · change vword (t.v .v3) e=_
    rw [w3 e he,k2.mem,k2.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep VChg)
open HighPack (packWidth)

def groupCode (g : Nat) : List Instr :=
  loadFour g++Impl.MlDsa.AArch64.Optimized.HighPack.packTail (packWidth g)

structure GroupPost (g block : Nat) (h a : Addr) (s t : State) : Prop where
  keep : Keep [.x9] s t
  vec : ∀r,r∉temps→t.v r=s.v r
  ready : Ready g t
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀i<2*packWidth g,t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (packed g s.mem h a)[2*packWidth g*block+i]!

 theorem group_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {h a : Addr} {s : State} (hr : Reduced s.mem a) (hc : Ready g s)
    (hp : s.gpr .x5=a+BitVec.ofNat 64 (64*block))
    (hhp : s.gpr .x4=h+BitVec.ofNat 64 (64*block))
    (ha : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hh : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6→InRegions s.wr (s.gpr .x1+8) 4)
    {rest : List Instr} {Q : State→Prop}
    (k : ∀t,GroupPost g block h a s t→WP isa (.block rest) t Q) :
    WP isa (.block (groupCode g++rest)) s Q := by
  unfold groupCode
  rw [List.append_assoc]
  refine loadFour_ok hg hc ha hh fun u hu cu hv=>?_
  refine HighPack.packTail_ok hg cu.toPackReady (by rw [hu.wr,hu.gpr];exact hw8)
    (fun h=>by rw [hu.wr,hu.gpr];exact hw4 h) fun t ht=>?_
  refine k t ⟨(hu.keep.trans ht.keep).mono (by decide),?_,?_,?_,?_⟩
  · intro r hr
    rw [ht.vec r (by intro h;exact hr (by simp only [temps,List.mem_cons,List.not_mem_nil,or_false] at *;grind only)),hu.get r hr]
  · refine ⟨ht.ready,?_,?_,?_⟩
    · intro e he;rw [ht.vec .v21 (by decide)];exact cu.factor e he
    · intro e he;rw [ht.vec .v22 (by decide)];exact cu.one e he
    · intro e he;rw [ht.vec .v23 (by decide)];exact cu.z e he
  · simpa only [hu.gpr,hu.mem] using ht.frame
  · intro i hi
    have hx:=ht.bytes i hi
    rw [hu.gpr] at hx
    rw [hx]
    exact packed_fields_byte hg hr cu.toPackConstants hb hi (by simpa only [hp,hhp] using hv)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)

def advance (g : Nat) : List Instr :=
  [.addImm .x .x4 .x4 64,.addImm .x .x5 .x5 64,.addImm .x .x1 .x1 (2*packWidth g),.subImm .x .x11 .x11 1]

theorem advance_ok (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (advance g)) s fun t =>
      t.gpr .x4=s.gpr .x4+64 ∧ t.gpr .x5=s.gpr .x5+64 ∧
      t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (2*packWidth g) ∧ t.gpr .x11=s.gpr .x11-1 ∧
      (∀r,r≠.x4→r≠.x5→r≠.x1→r≠.x11→t.gpr r=s.gpr r) ∧
      t.v=s.v ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  let a := s.write .x .x4 (s.gpr .x4+64)
  let b := a.write .x .x5 (a.gpr .x5+64)
  let c := b.write .x .x1 (b.gpr .x1+BitVec.ofNat 64 (2*packWidth g))
  let t := c.write .x .x11 (c.gpr .x11-1)
  refine WP.block_cons_iff.mpr ⟨a,rfl,?_⟩
  refine WP.block_cons_iff.mpr ⟨b,rfl,?_⟩
  refine WP.block_cons_iff.mpr ⟨c,?_,?_⟩
  · have hw : 2*packWidth g<4096 := by rcases hg with rfl|rfl <;> decide
    simp [isa,exec,hw,State.read,c]
  refine WP.block_cons_iff.mpr ⟨t,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [t,c,b,a]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [show Reg.x4≠.x11 by decide,show Reg.x4≠.x1 by decide,show Reg.x4≠.x5 by decide,
    show Reg.x5≠.x11 by decide,show Reg.x5≠.x1 by decide,show Reg.x5≠.x4 by decide,
    show Reg.x1≠.x11 by decide,show Reg.x1≠.x5 by decide,show Reg.x1≠.x4 by decide,
    show Reg.x11≠.x1 by decide,show Reg.x11≠.x5 by decide,show Reg.x11≠.x4 by decide,ite_false,ite_true,true_and]
  constructor
  · intro r h4 h5 h1 h11;simp only [h4,h5,h1,h11,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem Ready.sameVectors {g : Nat} {s t : State} (h : Ready g s) (hv : t.v=s.v) :
    Ready g t := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩,?_,?_,?_⟩
  · rw [hv]; exact h.add
  · rw [hv]; exact h.mul
  · rw [hv]; exact h.round
  · rw [hv]; exact h.modulus
  · rw [hv]; exact h.zero
  · rw [hv]; exact h.idx29
  · rw [hv]; exact h.idx24
  · rw [hv]; exact h.idx25
  · intro e he;rw [hv];exact h.factor e he
  · intro e he;rw [hv];exact h.one e he
  · intro e he;rw [hv];exact h.z e he

structure BodyPost (g block : Nat) (b a : Addr) (s t : State) : Prop where
  ready : Ready g t
  hints : t.gpr .x4=s.gpr .x4+64
  input : t.gpr .x5=s.gpr .x5+64
  output : t.gpr .x1=s.gpr .x1+BitVec.ofNat 64 (2*packWidth g)
  count : t.gpr .x11=s.gpr .x11-1
  gpr : ∀ r, r≠.x4 → r≠.x5 → r≠.x1 → r≠.x9 → r≠.x11 → t.gpr r=s.gpr r
  vec : ∀ r, r∉temps → t.v r=s.v r
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀ i<2*packWidth g, t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    (packed g s.mem b a)[(2*packWidth g)*block+i]!
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

/-- Complete loop body, including exact pointer and public counter updates. -/
theorem body_ok {g : Nat} (hg : IsG g) {block : Nat} (hb : block<16)
    {b a : Addr} {s : State} (hr : Reduced s.mem a) (hc : Ready g s)
    (hp : s.gpr .x5=a+BitVec.ofNat 64 (64*block))
    (hbptr : s.gpr .x4=b+BitVec.ofNat 64 (64*block))
    (hhin : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (16*j)) 16)
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (16*j)) 16)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6 → InRegions s.wr (s.gpr .x1+8) 4) :
    WP isa (.block (groupCode g ++ advance g)) s (BodyPost g block b a s) := by
  refine group_ok hg hb hr hc hp hbptr hin hhin hw8 hw4 fun u hu => ?_
  refine WP.mono (advance_ok u hg) fun t ht => ?_
  refine ⟨hu.ready.sameVectors ht.2.2.2.2.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.1,hu.keep.get .x4]
  · rw [ht.2.1,hu.keep.get .x5]
  · rw [ht.2.2.1,hu.keep.get .x1]
  · rw [ht.2.2.2.1,hu.keep.get .x11]
  · intro r h4 h0 h1 h9 h11
    rw [ht.2.2.2.2.1 r h4 h0 h1 h11,hu.keep.get r (by simpa using h9)]
  · intro r hr
    rw [ht.2.2.2.2.2.1,hu.vec r hr]
  · rw [ht.2.2.2.2.2.2.1]; exact hu.frame
  · intro i hi
    rw [ht.2.2.2.2.2.2.1]; exact hu.bytes i hi
  · exact ht.2.2.2.2.2.2.2.1.trans hu.keep.rd
  · exact ht.2.2.2.2.2.2.2.2.1.trans hu.keep.wr
  · exact ht.2.2.2.2.2.2.2.2.2.trans hu.keep.sp

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open HighPack (packWidth)
open VG.Proof.MlDsa.Arith (polyRegion)

 theorem packed_frame {g : Nat} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {b a : Addr}
    (hb : ∀r∈rs,(polyRegion b).Disjoint r) (ha : ∀r∈rs,(polyRegion a).Disjoint r) :
    packed g m' b a=packed g m b a := by
  unfold packed
  apply congrArg (fun L=>simpleBitPack L ((q-1)/(2*g)-1))
  apply Vector.ext
  intro i hi
  simp only [fields,Vector.getElem_ofFn]
  rw [VG.Proof.MlDsa.Arith.coeffAt_frame hf ha hi,VG.Proof.MlDsa.Arith.coeffAt_frame hf hb hi]

 theorem packed_length {g : Nat} (hg : Round.IsG g) (m : Mem) (b a : Addr) :
    (packed g m b a).length=32*packWidth g := by
  have hw : bitlen ((q-1)/(2*g)-1)=packWidth g := by rcases hg with rfl|rfl <;> rfl
  rw [packed,VG.Proof.MlDsa.Pack.simpleBitPack_eq,hw]
  exact VG.Proof.MlDsa.Pack.pack_length _ _ (by simp)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)
open VG.Proof.MlDsa.Arith (polyRegion)

structure LoopState (s₀ : State) (b a o : Addr) (g j : Nat) (s : State) : Prop where
  bound : j≤16
  ready : Ready g s
  values : ∀ i<(2*packWidth g)*j, s.mem (o+BitVec.ofNat 64 i)=(packed g s₀.mem b a)[i]!
  frame : Frame [⟨o,32*packWidth g⟩] s₀.mem s.mem
  hints : s.gpr .x4=b+BitVec.ofNat 64 (64*j)
  input : s.gpr .x5=a+BitVec.ofNat 64 (64*j)
  output : s.gpr .x1=o+BitVec.ofNat 64 ((2*packWidth g)*j)
  count : s.gpr .x11=BitVec.ofNat 64 (16-j)
  gpr : ∀ r, r≠.x4 → r≠.x5 → r≠.x1 → r≠.x9 → r≠.x11 → s.gpr r=s₀.gpr r
  vec : ∀ r, r∉temps → s.v r=s₀.v r
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  sp : s.sp=s₀.sp

theorem loop_step_ok {s₀ s : State} {b a o : Addr} {g j : Nat}
    (hg : IsG g) (hj : j<16) (h : LoopState s₀ b a o g j s)
    (hr : Reduced s₀.mem a) (hsep : (polyRegion a).Disjoint ⟨o,32*packWidth g⟩)
    (hbsep : (polyRegion b).Disjoint ⟨o,32*packWidth g⟩)
    (hhin : ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((b+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hin : ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : InRegions s₀.wr (o+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : packWidth g=6 → InRegions s₀.wr ((o+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (.block (groupCode g ++ advance g)) s (LoopState s₀ b a o g (j+1)) := by
  have sep : ∀ r∈[Region.mk o (32*packWidth g)], (polyRegion a).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hsep
  have red := VG.Proof.MlDsa.Arith.reduced_frame h.frame sep hr
  have bsep : ∀r∈[Region.mk o (32*packWidth g)],(polyRegion b).Disjoint r := by
    intro r hr;simp only [List.mem_singleton] at hr;subst r;exact hbsep
  have poly := packed_frame (g:=g) h.frame bsep sep
  refine WP.mono (body_ok hg hj red h.ready h.input h.hints
    (fun k hk=>by simpa only [h.rd,h.wr,h.hints] using hhin k hk)
    (fun k hk => by simpa only [h.rd,h.wr,h.input] using hin k hk)
    (by simpa only [h.wr,h.output] using hw8)
    (fun hw => by simpa only [h.wr,h.output] using hw4 hw)) ?_
  intro t ht
  have hf : Frame [⟨o+BitVec.ofNat 64 ((2*packWidth g)*j),2*packWidth g⟩] s.mem t.mem := by
    simpa only [h.output] using ht.frame
  have full : (2*packWidth g)*j+2*packWidth g≤32*packWidth g := by
    rcases hg with rfl | rfl
    · change 8*j+8≤128; omega_arith
    · change 12*j+12≤192; omega_arith
  have small : 32*packWidth g<2^64 := by rcases hg with rfl | rfl <;> decide
  refine ⟨by omega_arith,ht.ready,?_,?_,?_,?_,?_,?_,?_,?_,ht.rd.trans h.rd,ht.wr.trans h.wr,ht.sp.trans h.sp⟩
  · intro i hi
    rw [Nat.mul_succ] at hi
    by_cases old : i<(2*packWidth g)*j
    · rw [hf.bytes (R := ⟨o,(2*packWidth g)*j⟩) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        simpa only [BitVec.add_zero] using
          (Offset.disjoint o (d := 0) (n := (2*packWidth g)*j)
            (e := (2*packWidth g)*j) (k := 2*packWidth g)
            (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by dsimp; omega_arith) old]
      exact h.values i old
    · have hb := ht.bytes (i-(2*packWidth g)*j) (by omega_arith)
      rw [h.output,Offset.add_add,show (2*packWidth g)*j+(i-(2*packWidth g)*j)=i by omega_arith,poly] at hb
      exact hb
  · exact h.frame.trans (hf.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨⟨o,32*packWidth g⟩,by simp,Offset.sub_base o full⟩))
  · rw [ht.hints,h.hints]
    change (b+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 64=b+BitVec.ofNat 64 (64*(j+1))
    rw [Offset.add_add,Nat.mul_succ]
  · rw [ht.input,h.input]
    change (a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 64=a+BitVec.ofNat 64 (64*(j+1))
    rw [Offset.add_add,Nat.mul_succ]
  · rw [ht.output,h.output,Offset.add_add,Nat.mul_succ]
  · rw [ht.count,h.count]; bv_omega
  · intro r h4 h0 h1 h9 h11
    exact (ht.gpr r h4 h0 h1 h9 h11).trans (h.gpr r h4 h0 h1 h9 h11)
  · intro r hv
    exact (ht.vec r hv).trans (h.vec r hv)


/-- The exact loop executes sixteen groups and establishes the complete
encoded output while preserving the original input polynomial. -/
theorem loop_ok {s₀ s : State} {b a o : Addr} {g start : Nat}
    (hg : IsG g) (hstart : start<16) (h : LoopState s₀ b a o g start s)
    (hr : Reduced s₀.mem a) (hsep : (polyRegion a).Disjoint ⟨o,32*packWidth g⟩)
    (hbsep : (polyRegion b).Disjoint ⟨o,32*packWidth g⟩)
    (hhin : ∀ j<16,∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((b+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hin : ∀ j<16, ∀ k<4, InRegions (s₀.rd++s₀.wr)
      ((a+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : ∀ j<16, InRegions s₀.wr (o+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : ∀ j<16, packWidth g=6 → InRegions s₀.wr ((o+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (.loop (.block (groupCode g ++ advance g)) (.nonzero .x .x11)) s
      (LoopState s₀ b a o g 16) := by
  let I : Nat → State → Prop := fun left t => ∃ j, j<16 ∧ left=16-j ∧ LoopState s₀ b a o g j t
  refine WP.loop (M := isa) I (fun left t ⟨j,hj,hl,ht⟩ => ?_) (16-start) s ⟨start,hstart,rfl,h⟩
  refine WP.mono (loop_step_ok hg hj ht hr hsep hbsep (hhin j hj) (hin j hj) (hw8 j hj) (hw4 j hj)) ?_
  intro u hu
  by_cases hend : j+1=16
  · left
    refine ⟨?_,hend ▸ hu⟩
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu.count,hend,Nat.sub_self]
    rfl
  · right
    refine ⟨?_,16-(j+1),by omega_arith,j+1,by omega_arith,rfl,hu⟩
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu.count,Option.some.injEq,bne_iff_ne]
    bv_omega


/-- At loop completion, the complete output buffer is the original encoding. -/
theorem LoopState.output_bytes {s₀ s : State} {b a o : Addr} {g : Nat}
    (hg : IsG g) (h : LoopState s₀ b a o g 16 s) :
    VG.Spec.Sha3.bytesAt s.mem o (32*packWidth g)=packed g s₀.mem b a := by
  apply List.ext_getElem
  · simp only [VG.Spec.Sha3.bytesAt,List.length_map,List.length_range,packed_length hg]
  · intro i hi hj
    simp only [VG.Spec.Sha3.bytesAt,List.getElem_map,List.getElem_range]
    rw [←getElem!_pos (packed g s₀.mem b a) i hj]
    apply h.values
    have hh : i<32*packWidth g := by
      simpa only [VG.Spec.Sha3.bytesAt,List.length_map,List.length_range] using hi
    have he : 2*packWidth g*16=32*packWidth g := by omega_arith
    omega_arith

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end

end


/-! ## From `UseHintPackSpec.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.Spec.MlDsa

theorem fields_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {m : Mem} {h a : Addr} (ha : Reduced m a) :
    fields g m h a = Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
      ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m a) := by
  apply Vector.ext
  intro i hi
  simp only [fields,Vector.getElem_ofFn,Vector.getElem_zipWith]
  rw [value_spec hg (ha i hi)]
  have hpoly : (⟨(coeffAt m a i).toNat,ha i hi⟩ : Zq)=(polyAt m a)[i] :=
    Fin.ext (VG.Proof.MlDsa.Pack.polyAt_val ha hi).symm
  have hh := VG.Proof.MlDsa.Round.hintAt_get m h hi
  rw [VG.Proof.MlDsa.Round.getElem!_eq _ hi] at hh
  rw [hpoly,hh]

theorem packed_spec {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    {m : Mem} {h a : Addr} (ha : Reduced m a) :
    packed g m h a = simpleBitPack
      (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
        ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m a)) ((q-1)/(2*g)-1) := by
  rw [packed,fields_spec hg ha]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open HighPack
open VG.Proof.MlDsa.AArch64.Round

 theorem setup_ready (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.HighPack.constants g++Impl.MlDsa.AArch64.Optimized.HighPack.packSetup)) s fun t=>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] s t ∧ Ready g t := by
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok s g) fun a ha=>?_
  refine WP.mono (packSetup_ok a) fun t ht=>?_
  obtain ⟨hk,_,h17,h18,h19,h20,h21,h22,h23⟩ := ha
  refine ⟨hk.trans ht.1,⟨⟨?_,?_,?_,?_⟩,⟨ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩⟩,?_,?_,?_⟩
  · intro e he;rw [ht.1.vec .v17 (by decide),h17,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v18 (by decide),h18,repeatedWord_lane _ he]
    rcases hg with rfl|rfl <;> rfl
  · intro e he;rw [ht.1.vec .v19 (by decide),h19,repeatedWord_lane _ he]
    rcases hg with rfl|rfl <;> rfl
  · intro e he;rw [ht.1.vec .v20 (by decide),h20,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v21 (by decide),h21,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v22 (by decide),h22,repeatedWord_lane _ he];rfl
  · intro e _;rw [ht.1.vec .v23 (by decide),h23];simp [vword]

 theorem code_eq (g : Nat) : Impl.MlDsa.AArch64.Optimized.UseHintPack.code g=
    .seq (.block (Impl.MlDsa.AArch64.Optimized.HighPack.constants g++
      Impl.MlDsa.AArch64.Optimized.HighPack.packSetup++([.movz .x .x11 16 0] : List Instr)))
      (.loop (.block (groupCode g++advance g)) (.nonzero .x .x11)) := by
  simp only [Impl.MlDsa.AArch64.Optimized.UseHintPack.code,groupCode,loadFour,advance,packWidth,
    beq_iff_eq,List.append_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackCode.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)
open VG.Proof.MlDsa.Arith (polyRegion)
open VG.Proof.MlKem.AArch64 (Keep)

structure CodePost (g : Nat) (s t : State) : Prop where
  keep : Keep [.x4,.x5,.x1,.x9,.x11] s t
  frame : Frame [⟨s.gpr .x1,32*packWidth g⟩] s.mem t.mem
  bytes : VG.Spec.Sha3.bytesAt t.mem (s.gpr .x1) (32*packWidth g)=
    packed g s.mem (s.gpr .x4) (s.gpr .x5)

/-- Complete correctness of the exact selected packing function, including
setup, fixed-count loop, output frame, and callee-saved registers. -/
theorem code_ok {g : Nat} (hg : IsG g) (s : State)
    (hr : Reduced s.mem (s.gpr .x5))
    (hsep : (polyRegion (s.gpr .x5)).Disjoint ⟨s.gpr .x1,32*packWidth g⟩)
    (hbsep : (polyRegion (s.gpr .x4)).Disjoint ⟨s.gpr .x1,32*packWidth g⟩)
    (hhin : ∀j<16,∀k<4,InRegions (s.rd++s.wr)
      ((s.gpr .x4+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hin : ∀ j<16, ∀ k<4, InRegions (s.rd++s.wr)
      ((s.gpr .x5+BitVec.ofNat 64 (64*j))+BitVec.ofNat 64 (16*k)) 16)
    (hw8 : ∀ j<16, InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 ((2*packWidth g)*j)) 8)
    (hw4 : ∀ j<16, packWidth g=6 → InRegions s.wr
      ((s.gpr .x1+BitVec.ofNat 64 ((2*packWidth g)*j))+8) 4) :
    WP isa (Impl.MlDsa.AArch64.Optimized.UseHintPack.code g) s (CodePost g s) := by
  rw [code_eq]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (setup_ready s hg) fun a ha => ?_
  let u := a.write .x .x11 16
  refine WP.block_cons_iff.mpr ⟨u,rfl,WP.block_nil_iff.mpr ?_⟩
  have um : u.mem=s.mem := ha.1.mem
  have ur : u.rd=s.rd := ha.1.rd
  have uw : u.wr=s.wr := ha.1.wr
  have up : u.sp=s.sp := ha.1.sp
  have ug (r : Reg) (h9 : r≠.x9) (h11 : r≠.x11) : u.gpr r=s.gpr r := by
    change (if r=.x11 then 16 else a.gpr r)=s.gpr r
    rw [ite_eq_right h11,ha.1.gpr r h9]
  have initial : LoopState u (s.gpr .x4) (s.gpr .x5) (s.gpr .x1) g 0 u := by
    refine ⟨by decide,ha.2.sameVectors rfl,?_,Frame.refl _ _,?_,?_,?_,rfl,
      fun _ _ _ _ _ _ => rfl,fun _ _ => rfl,rfl,rfl,rfl⟩
    · intro i hi; omega
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x4 (by decide) (by decide)
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x5 (by decide) (by decide)
    · simpa only [Nat.mul_zero,BitVec.add_zero] using ug .x1 (by decide) (by decide)
  refine WP.mono (loop_ok hg (by decide) initial (by rw [um]; exact hr) hsep hbsep
    (fun j hj k hk=>by rw [ur,uw];exact hhin j hj k hk)
    (fun j hj k hk => by rw [ur,uw]; exact hin j hj k hk)
    (fun j hj => by rw [uw]; exact hw8 j hj)
    (fun j hj hw => by rw [uw]; exact hw4 j hj hw)) fun t ht => ?_
  refine ⟨?_,?_,?_⟩
  · refine ⟨?_,ht.rd.trans ur,ht.wr.trans uw,ht.sp.trans up,?_⟩
    · intro r hn
      have hh : r≠.x4 ∧ r≠.x5 ∧ r≠.x1 ∧ r≠.x9 ∧ r≠.x11 := by simpa using hn
      rw [ht.gpr r hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2,ug r hh.2.2.2.1 hh.2.2.2.2]
    · intro r hr
      have htemp : r∉temps := by
        simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hc : r∉[VReg.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] := by
        simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [ht.vec r htemp]
      change (a.v r).extractLsb' 0 64=(s.v r).extractLsb' 0 64
      rw [ha.1.vec r hc]
  · simpa only [um] using ht.frame
  · simpa only [um] using ht.output_bytes hg

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackProg.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)
open HighPack (packWidth)
open VG.Proof.MlKem.AArch64 (Keep)

structure Pre (g : Nat) (s : State) : Prop where
  gamma : arg32 s .x3=g
  reduced : Reduced s.mem (s.gpr .x2)
  input : InRegions (s.rd++s.wr) (s.gpr .x2) 1024
  hints : InRegions (s.rd++s.wr) (s.gpr .x1) 1024
  output : InRegions s.wr (s.gpr .x0) (32*packWidth g)
  sep : (polyRegion (s.gpr .x2)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩
  hintSep : (polyRegion (s.gpr .x1)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩

structure Post (g : Nat) (s t : State) : Prop where
  frame : Frame [⟨s.gpr .x0,32*packWidth g⟩] s.mem t.mem
  bytes : VG.Spec.Sha3.bytesAt t.mem (s.gpr .x0) (32*packWidth g)=
    packed g s.mem (s.gpr .x1) (s.gpr .x2)

private theorem subregion {rs : List Region} {p : Addr} {len off n : Nat}
    (h : InRegions rs p len) (hb : off+n≤len) (ho : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) n := by
  obtain ⟨r,hr,hp⟩ := h
  exact ⟨r,hr,VG.CallLay.contains_trans hp hb ho⟩

/-- Dispatch accepts the ABI's 32-bit gamma argument; its upper register bits are irrelevant. -/
theorem prog_ok {g : Nat} (hg : IsG g) {s : State} (hp : Pre g s) :
    WP isa Impl.MlDsa.AArch64.Optimized.UseHintPack.prog s (Post g s) := by
  unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
  apply WP.seq
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x4,.x5,.x1]
    (Q:=fun a=>a.gpr .x4=s.gpr .x1 ∧ a.gpr .x5=s.gpr .x2 ∧
      a.gpr .x1=s.gpr .x0 ∧ a.mem=s.mem)
    (by arun) (by decide +kernel) (hv:=rfl)) fun a ha=>?_
  apply zext_ok
  apply onGamma_ok (by decide : Reg.x6≠.x3)
  · rw [zextS_toNat]
    have hh : arg32 a .x3=g := by
      unfold arg32; rw [ha.2.get .x3 (by decide)]; exact hp.gamma
    rw [hh]; exact hg
  · intro g' he b hk hm
    have hsame : g'=g := by
      rw [zextS_toNat] at he
      unfold arg32 at he
      rw [ha.2.get .x3 (by decide)] at he
      exact he.symm.trans hp.gamma
    rw [hsame]
    have bm : b.mem=s.mem := hm.trans ha.1.2.2.2
    have br : b.rd=s.rd := hk.rd.trans ha.2.rd
    have bw : b.wr=s.wr := hk.wr.trans ha.2.wr
    have bh : b.gpr .x4=s.gpr .x1 := by
      rw [hk.get .x4 (by decide),zextS_other _ (by decide)]; exact ha.1.1
    have bi : b.gpr .x5=s.gpr .x2 := by
      rw [hk.get .x5 (by decide),zextS_other _ (by decide)]; exact ha.1.2.1
    have bo : b.gpr .x1=s.gpr .x0 := by
      rw [hk.get .x1 (by decide),zextS_other _ (by decide)]; exact ha.1.2.2.1
    refine WP.mono (code_ok hg b (by rw [bm,bi];exact hp.reduced)
      (by rw [bi,bo];exact hp.sep) (by rw [bh,bo];exact hp.hintSep) ?_ ?_ ?_ ?_) fun t ht=>?_
    · intro j hj k hk
      rw [br,bw,bh,Offset.add_add]
      exact subregion hp.hints (by omega_using [hj, hk]) (by omega_using [])
    · intro j hj k hk
      rw [br,bw,bi,Offset.add_add]
      exact subregion hp.input (by omega_using [hj, hk]) (by omega_using [])
    · intro j hj
      rw [bw,bo]
      apply subregion hp.output
      · rcases hg with rfl|rfl
        · change 8*j+8≤128;omega_using [hj]
        · change 12*j+8≤192;omega_using [hj]
      · rcases hg with rfl|rfl <;> decide
    · intro j hj hw
      rw [bw,bo]
      change InRegions s.wr ((s.gpr .x0+BitVec.ofNat 64 (2*packWidth g*j))+BitVec.ofNat 64 8) 4
      rw [Offset.add_add]
      apply subregion hp.output
      · rw [hw];omega_using [hj]
      · rw [hw];omega_using []
    · exact ⟨by simpa only [bm,bo] using ht.frame,
        by simpa only [bm,bo,bh,bi] using ht.bytes⟩

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end
