module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.ReadCache
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Verify
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCall
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVerified
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Pack.Bits
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.MlDsa.Pack.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.AArch64.Optimized.UseHintPackTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.UseHintPackProg`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.UseHintPackWord`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Impl.MlDsa.AArch64.Round

def csub (m a : BitVec 32) : BitVec 32 := if a.toNat≤(a-m).toNat then a else a-m

def before (g : Nat) (a h : BitVec 32) : BitVec 32 :=
  let f := HighPack.raw g a
  let delta := ((f*BitVec.ofNat 32 (2*g)-a) >>> 31 <<< 1)-1
  f+(if h=0 then 0 else delta)+BitVec.ofNat 32 (dMod g)

def value (g : Nat) (a h : BitVec 32) : BitVec 32 :=
  csub (BitVec.ofNat 32 (dMod g)) (csub (BitVec.ofNat 32 (dMod g)) (before g a h))

 theorem csub_toNat {m a : BitVec 32} (hm : m.toNat<2^31) (ha : a.toNat<2^31) :
    (csub m a).toNat=if a.toNat<m.toNat then a.toNat else a.toNat-m.toNat := by
  by_cases hz : m=0
  · subst m; simp [csub]
  have hmpos : 0<m.toNat := by bv_omega
  unfold csub
  by_cases h : a.toNat<m.toNat
  · rw [ite_eq_left (by bv_omega),ite_eq_left h]
  · rw [ite_eq_right (by bv_omega),ite_eq_right h,BitVec.toNat_sub]
    omega_arith

 theorem sub_sign {x y : BitVec 32} (hx : x.toNat<2^31) (hy : y.toNat<2^31) :
    (x-y) >>> 31=if x.toNat<y.toNat then 1 else 0 := by
  by_cases h : x.toNat<y.toNat
  · rw [ite_eq_left h]; bv_omega
  · rw [ite_eq_right h]; bv_omega

 theorem signed_adjust {f m : BitVec 32} (hf : f.toNat≤44) (hm : m.toNat≤44)
    (hpos : 0<m.toNat) (b : Bool) :
    ((f+((if b then (1 : BitVec 32) else 0) <<< 1)-1)+m).toNat=
      if b then f.toNat+m.toNat+1 else f.toNat+m.toNat-1 := by
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · bv_omega
  · bv_omega

 theorem before_toNat {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (before g a h).toNat =
      if h≠0 then (if hbF g a.toNat*(2*g)<a.toNat then hbF g a.toNat+hbM g+1
        else hbF g a.toNat+hbM g-1) else hbF g a.toNat+hbM g := by
  have hf := HighPack.raw_toNat hg ha
  have hb := hbF_le (mem_of_isG hg) ha
  have hm := hbM_pos hg
  have hm16 : 16≤hbM g := by rcases hg with rfl|rfl <;> decide
  have hm44 : hbM g≤44 := by rcases hg with rfl|rfl <;> decide
  have hg2 : 2*g≤523776 := by rcases hg with rfl|rfl <;> decide
  have hd : (BitVec.ofNat 32 (dMod g)).toNat=hbM g := by
    rw [BitVec.toNat_ofNat,dMod_eq hg]; omega_arith
  have hp : (HighPack.raw g a * BitVec.ofNat 32 (2*g)).toNat=hbF g a.toNat*(2*g) := by
    rw [BitVec.toNat_mul,hf,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show 2*g<2^32 by omega_arith)]
    have := Nat.mul_le_mul (Nat.le_trans hb hm44) hg2
    exact Nat.mod_eq_of_lt (by omega_arith)
  have hq : q=8380417 := rfl
  have hpbound := Nat.mul_le_mul (Nat.le_trans hb hm44) hg2
  dsimp only [before]
  by_cases hh : h=0
  · rw [ite_eq_left hh,ite_eq_right (by exact not_not_intro hh),BitVec.toNat_add,BitVec.toNat_add,hf,hd]
    change ((hbF g a.toNat+0)%2^32+hbM g)%2^32=_
    omega_arith
  · rw [ite_eq_right hh,ite_eq_left hh]
    have hsign := sub_sign (x:=HighPack.raw g a * BitVec.ofNat 32 (2*g)) (y:=a)
      (by rw [hp]; omega_arith) (by omega_arith)
    rw [hp] at hsign
    rw [hsign]
    have hh := signed_adjust (f:=HighPack.raw g a) (m:=BitVec.ofNat 32 (dMod g))
      (by rw [hf]; omega_arith) (by rw [hd]; omega_arith) (by rw [hd]; omega_arith)
      (decide (hbF g a.toNat*(2*g)<a.toNat))
    simp only [decide_eq_true_eq] at hh
    rw [hf,hd] at hh
    have he (f d : BitVec 32) : f+(d-1)=f+d-1 := by bv_omega
    rw [he]
    exact hh

 theorem value_toNat {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (value g a h).toNat =
      (if h≠0 then (if hbF g a.toNat*(2*g)<a.toNat then hbF g a.toNat+hbM g+1
        else hbF g a.toNat+hbM g-1) else hbF g a.toNat+hbM g)%hbM g := by
  have hv := before_toNat hg (h:=h) ha
  have hf := hbF_le (mem_of_isG hg) ha
  have hm := hbM_pos hg
  have hm16 : 16≤hbM g := by rcases hg with rfl|rfl <;> decide
  have hm44 : hbM g≤44 := by rcases hg with rfl|rfl <;> decide
  have hd : (BitVec.ofNat 32 (dMod g)).toNat=hbM g := by
    rw [BitVec.toNat_ofNat,dMod_eq hg]; omega_arith
  have hb : (before g a h).toNat<3*hbM g := by rw [hv]; (repeat' split) <;> omega_arith
  have hc := csub_toNat (m:=BitVec.ofNat 32 (dMod g)) (a:=before g a h)
    (by rw [hd]; omega_arith) (by omega_arith)
  rw [hd] at hc
  have hc2 := csub_toNat (m:=BitVec.ofNat 32 (dMod g))
    (a:=csub (BitVec.ofNat 32 (dMod g)) (before g a h))
    (by rw [hd]; omega_arith) (by rw [hc]; split <;> omega_arith)
  rw [hd,hc] at hc2
  change (csub _ (csub _ _)).toNat=_
  rw [hc2,←hv]
  by_cases h1 : (before g a h).toNat<hbM g
  · simp only [ite_eq_left h1,Nat.mod_eq_of_lt h1]
  · rw [ite_eq_right h1,Nat.mod_eq_sub_mod (by omega_arith)]
    by_cases h2 : (before g a h).toNat-hbM g<hbM g
    · rw [ite_eq_left h2,Nat.mod_eq_of_lt h2]
    · rw [ite_eq_right h2,Nat.mod_eq_sub_mod (by omega_arith),Nat.mod_eq_of_lt (by omega_arith)]

 theorem value_spec {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (value g a h).toNat=(useHint g (decide (h≠0)) ⟨a.toNat,ha⟩).toNat := by
  rw [value_toNat hg ha,useHint_eq (mem_of_isG hg)]
  simp only [decide_eq_true_eq]
  rfl

 theorem value_lt {g : Nat} (hg : IsG g) {a h : BitVec 32} (ha : a.toNat<q) :
    (value g a h).toNat<hbM g := by
  rw [value_toNat hg ha]
  exact Nat.mod_lt _ (hbM_pos hg)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end

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

end

end

/-! ## From `UseHintPackContract.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)
open HighPack (packWidth)

def packK (g : Nat) : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x1),polyRegion (s.gpr .x2)] ∧
    s.wr=[⟨s.gpr .x0,32*packWidth g⟩] ∧
    (polyRegion (s.gpr .x1)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩ ∧
    (polyRegion (s.gpr .x2)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩ ∧
    arg32 s .x3=g ∧ Reduced s.mem (s.gpr .x2)
  post s t := Spec.Sha3.bytesAt t.mem (s.gpr .x0) (32*packWidth g)=
    packed g s.mem (s.gpr .x1) (s.gpr .x2)
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧
    s.gpr .x2=t.gpr .x2 ∧ (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32 ∧ s.sp=t.sp

theorem pack_pre {g : Nat} {s : State} (hp : (packK g).pre s) : Pre g s := by
  obtain ⟨rd,wr,hs,ws,hg,hr⟩ := hp
  refine ⟨hg,hr,?_,?_,?_,ws,hs⟩
  · rw [rd];exact ⟨polyRegion (s.gpr .x2),by simp,Region.contains_self _ _⟩
  · rw [rd];exact ⟨polyRegion (s.gpr .x1),by simp,Region.contains_self _ _⟩
  · rw [wr];exact ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩

/-- Full selected program satisfies the AArch64 calling convention. -/
theorem pack_correct {g : Nat} (hg : IsG g) (s : State) (hp : (packK g).pre s) :
    ∃ tr t, Exec isa Impl.MlDsa.AArch64.Optimized.UseHintPack.prog s tr t ∧
      abiPreserved s t ∧ (packK g).post s t := by
  obtain ⟨tr,t,he,ht⟩ := prog_ok hg (pack_pre hp)
  exact ⟨tr,t,he,VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he,ht.bytes⟩

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round

private def shuffled (s : State) : State :=
  ((s.write .x .x4 (s.gpr .x1)).write .x .x5 (s.gpr .x2)).write .x .x1 (s.gpr .x0)

private theorem shuffled_exec (s : State) :
    Exec isa (.block [.addImm .x .x4 .x1 0,.addImm .x .x5 .x2 0,.addImm .x .x1 .x0 0])
      s [] (shuffled s) := by
  apply Exec.block
  simp [shuffled,execBlock,isa,exec,addrs,State.read,State.write]

private theorem body_ct :
    ConstantTime isa (fun _=>True)
      (fun s t=>s.sp=t.sp ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x4=t.gpr .x4 ∧
        s.gpr .x5=t.gpr .x5 ∧ (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32)
      (zext .x3 (onGamma .x3 .x6 Impl.MlDsa.AArch64.Optimized.UseHintPack.code)) := by
  apply zext_ct (τ:=Taint.ofRegs [.x3,.x1,.x4,.x5])
  · intro s t h
    apply agree_zext h.1 h.2.2.2.2
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
  · taint_decide

/-- Data and hint values stay secret; only pointers and the low32 public gamma are related. -/
theorem pack_ct {g : Nat} : ConstantTime isa (packK g).pre (packK g).pub
    Impl.MlDsa.AArch64.Optimized.UseHintPack.prog := by
  intro s t l r s' t' _ _ hp hs ht
  cases hs with | seq a b =>
    cases ht with | seq c d =>
      obtain ⟨rfl,rfl⟩ := Exec.det a (shuffled_exec s)
      obtain ⟨rfl,rfl⟩ := Exec.det c (shuffled_exec t)
      apply body_ct _ _ _ _ _ _ trivial trivial ?_ b d
      rcases hp with ⟨h0,h1,h2,h3,hsp⟩
      simpa [shuffled,State.write] using And.intro hsp (And.intro h0 (And.intro h1 (And.intro h2 h3)))

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedRowStart`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized

abbrev W (p : Params) (σ : State) (A' : Nat→Nat→Poly) (r : Nat) (s : State) : Prop :=
  PolyIs s.mem (pa s (wP p)) ((rDot p σ A' r).map (·*montgomeryRInv))

theorem unpack_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A' : Nat→Nat→Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s) :
    WP isa (unpackT1At P (.x25,32+320*r) (tmP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧ PolyIs t.mem (pa t (tmP p)) (rU p σ r) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr;have hpk:=hF.pk
  have hc : rwChk (vR p) (vW p) (.x25,32+320*r) 320 (tmP p) 1024=true := by unfold rwChk;vlay
  refine WP.mono_syms (t1At_ok hP.s64 hP.unpackT1 L hc) fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;vlay) h24,
    L.keepPoly hb (by vlayd) hw,?_⟩
  rw [hs.vc.pkSlice (by rw [hF.pk];omega_using [hr])] at hv
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  exact hv

theorem nttT_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PolyIs s.mem (pa s (tmP p)) (rU p σ r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.forward (tmP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧
      PosPolyIs t.mem (pa t (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wr : inB (vW p) (tmP p) 1024=true := by vlayd
  refine WP.mono_syms (Sign.positiveNttAt_layout L rd wr
    ⟨hs.roots.nttTableAt (L.inW wr),hs.roots.forward.readable⟩ ht.1)
    fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wr) h24,
    L.keepPoly hb (by vlayd) hw,?_⟩
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  rw [ht.2] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedRowProduct`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.MontProductCallTiming`, which this module and modules that import it used -/

section

/-! ## From `MontProductCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) : CalleeOk S code (montProductContract abi) :=
  CalleeOk.of_ct verified.1 verified.2.1 (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev args (out a b : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b)]

structure Ready (out a b : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  outA : (polyRegion (pa s out)).Disjoint (polyRegion (pa s a))
  outB : (polyRegion (pa s out)).Disjoint (polyRegion (pa s b))
  positiveA : PositiveReduced s.mem (pa s a)
  positiveB : PositiveReduced s.mem (pa s b)
  readable : Covers [polyRegion (pa s a),polyRegion (pa s b),polyRegion (pa s out)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s out)] s.wr

theorem at_pre {s s1 : State} {out a b : Ptr}
    (h : Ready out a b s) (h1 : Args (args out a b) s s1) :
    (montProductContract abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s a),polyRegion (pa s b)] [polyRegion (pa s out)]) := by
  sig_pre [montProductContract,montProductSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  exact ⟨trivial,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,h.positiveA,h.positiveB⟩

theorem args_ok {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : Ready out a b s) :
    WP isa (callAt nm code (args out a b)) s fun t =>
      Post S s t [polyRegion (pa s out)] ∧
      PolyIs t.mem (pa s out) (montgomeryMultiplyNTT (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b))) := by
  refine WP.mono (callAtSyms_ok hS (callee S) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [montProductContract,montProductSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

/-! ## From `MontProductCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem at_tr {S : Nat} {nm : String} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → Ready out a b x ∧ Ready out a b z ∧
      pa x out=pa z out ∧ pa x a=pa z a ∧ pa x b=pa z b ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm code (args out a b)) fun _ _=>True := by
  refine callAtSyms_tr (callee S) (args_ok ho ha hb) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,eo,ea,eb,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x a),polyRegion (pa x b)],[polyRegion (pa x out)],
    at_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb]; exact at_pre rz h2
  · sig_pub [montProductContract,montProductSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,eo,ea,eb⟩
  · rw [eo,ea,eb]; exact rz.readable
  · rw [eo]; exact rz.writable
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Arith.Montgomery

theorem product_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.product p) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧
      PolyIs t.mem (pa t (tm2P p))
        (montgomeryMultiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : PosPolyIs s.mem (pa s (cP p)) (ntt c0) := hs.c
  have ro : inB (vR p++vW p) (tm2P p) 1024=true := by vlayd
  have ra : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have rb : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wo : inB (vW p) (tm2P p) 1024=true := by vlayd
  have ready : MontProduct.Ready (tm2P p) (cP p) (tmP p) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),hc.bound,ht.bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  refine WP.mono_syms (MontProduct.at_ok L.s64 (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(tm2P p,1024)] := hp'.b
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hp'.cs .x24 (by decide) (by decide)),L.keepPoly hb (by vlayd) hw,?_⟩
  rw [hb.pa (L.ptrBs ro)]
  rwa [hc.value,ht.value] at hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedDot`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.MontDotCallTiming`, which this module and modules that import it used -/

section

/-! ## From `MontDotCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontDot (dot)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) {count : Nat} (hc : count=4∨count=5∨count=7) : CalleeOk S (dot count) (montDotContract abi count) :=
  CalleeOk.of_ct (verified hc).1 (verified hc).2.1 (by rcases hc with rfl|rfl|rfl <;> lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev args (out a b : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b)]

def family (p : Addr) (n : Nat) : Region := ⟨p,1024*n⟩

structure Ready (count : Nat) (out a b : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024*count≤2^64
  bFit : (pa s b).toNat+1024*count≤2^64
  outA : (polyRegion (pa s out)).Disjoint (family (pa s a) count)
  outB : (polyRegion (pa s out)).Disjoint (family (pa s b) count)
  positiveA : ∀j<count,PositiveReduced s.mem (pa s a+BitVec.ofNat 64 (1024*j))
  positiveB : ∀j<count,PositiveReduced s.mem (pa s b+BitVec.ofNat 64 (1024*j))
  readable : Covers [family (pa s a) count,family (pa s b) count,polyRegion (pa s out)] (s.rd++s.wr)
  writable : Covers [polyRegion (pa s out)] s.wr

theorem at_pre {s s1 : State} {count : Nat} {out a b : Ptr}
    (h : Ready count out a b s) (h1 : Args (args out a b) s s1) :
    (montDotContract abi count).pre
      (s1.callEntry.withRegions [family (pa s a) count,family (pa s b) count] [polyRegion (pa s out)]) := by
  sig_pre [montProductContract,montDotSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1,Arg.val]
  have he : 256*count*4=1024*count := by omega_using []
  rw [he]
  exact ⟨rfl,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,h.positiveA,h.positiveB⟩

theorem args_ok {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {count : Nat} (hc : count=4∨count=5∨count=7) {nm : String} {s : State} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : Ready count out a b s) :
    WP isa (callAt nm (dot count) (args out a b)) s fun t =>
      Post S s t [polyRegion (pa s out)] ∧
      PolyIs t.mem (pa s out) ((dotNTT (fun j=>polyAt s.mem (pa s a+BitVec.ofNat 64 (1024*j)))
        (fun j=>polyAt s.mem (pa s b+BitVec.ofNat 64 (1024*j))) count).map (·*montgomeryRInv)) := by
  refine WP.mono (callAtSyms_ok hS (callee S hc) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [montProductContract,montDotSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

/-! ## From `MontDotCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MontDot (dot)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem at_tr {S : Nat} {count : Nat} (hc : count=4∨count=5∨count=7) {nm : String} {out a b : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → Ready count out a b x ∧ Ready count out a b z ∧
      pa x out=pa z out ∧ pa x a=pa z a ∧ pa x b=pa z b ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm (dot count) (args out a b)) fun _ _=>True := by
  refine callAtSyms_tr (callee S hc) (args_ok ho ha hb) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,eo,ea,eb,esp⟩ := hQ x z hp
  refine ⟨[family (pa x a) count,family (pa x b) count],[polyRegion (pa x out)],
    at_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb]; exact at_pre rz h2
  · sig_pub [montDotContract,montDotSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,eo,ea,eb⟩
  · rw [eo,ea,eb]; exact rz.readable
  · rw [eo]; exact rz.writable
end VG.Proof.MlDsa.AArch64.Optimized.MontDot

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (zHat dotAcc foldl_dot)

private theorem poly_addr (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j)))=
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem dot_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.dot p r) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) ((dotAcc p (vSig p σ) A' r p.ℓ).map (·*montgomeryRInv)) := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hrow : p.ℓ*r+p.ℓ≤p.k*p.ℓ := by
    have hm:=Nat.mul_le_mul_left p.ℓ (show r+1≤p.k by omega_using [hr])
    rw [Nat.mul_succ,Nat.mul_comm p.ℓ p.k] at hm
    exact hm
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  have ro : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have ra : inB (vR p++vW p) (aP (p.ℓ*r)) (1024*p.ℓ)=true := by vlayd
  have rb : inB (vR p++vW p) (zP p 0) (1024*p.ℓ)=true := by vlayd
  have wo : inB (vW p) (wP p) 1024=true := by vlayd
  have hA j (hj : j<p.ℓ) : PolyIs s.mem (pa s (aP (p.ℓ*r))+BitVec.ofNat 64 (1024*j)) (A' r j) := by
    have hv:=hs.a r hr j hj
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*r+j)))) _ at hv
    rwa [poly_addr] at hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem (pa s (zP p 0)+BitVec.ofNat 64 (1024*j)) (zHat p (vSig p σ) j) := by
    have hv:=hs.z j hj
    simp only [Stored,decide_eq_true_eq.mpr hj,↓reduceIte,ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+(1+p.k+j))))) _ at hv
    have he : p.k*p.ℓ+(1+p.k+j)=(p.k*p.ℓ+(1+p.k))+j := by omega_using []
    rw [he,poly_addr] at hv
    simpa only [zP,vP,Nat.add_zero] using hv
  have ready : MontDot.Ready p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),
      fun j hj=>(PosPolyIs.of_canonical (hA j hj)).bound,fun j hj=>(hB j hj).bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  refine WP.mono_syms (MontDot.at_ok L.s64 hn (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hP,hv⟩ hy=>?_
  have hb : PPostB S s t [(wP p,1024)] := hP.b
  have hw : w1Len p * r ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) (Nat.le_of_lt hr); rw [Nat.mul_comm (w1Len p) p.k] at this
    have := hF.w1; omega_arith
  have hc : SCChk p r [(wP p, 1024)] :=
    SCChk.x28 hF (Nat.le_of_lt hr) (.inr (by simp only [SV, oP]; omega_using [])) (.inr (by simp only [oP]; omega_using []))
      (.inr (by simp only [oP]; omega_using [hw])) (.inr (by simp only [oP]; omega_using [])) (by rw [hsc]; simp only [oP]; omega_using [])
  refine ⟨hs.keep hF hp hb hc hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hP.cs .x24 (by decide) (by decide)),?_⟩
  rw [hb.pa (L.ptrBs ro)]
  have he : dotNTT (fun j=>polyAt s.mem (pa s (aP (p.ℓ*r))+BitVec.ofNat 64 (1024*j)))
      (fun j=>polyAt s.mem (pa s (zP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ=
      dotAcc p (vSig p σ) A' r p.ℓ := by
    unfold dotNTT
    rw [←foldl_dot]
    apply congrArg (List.foldl add zero)
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    dsimp only
    rw [(hA j hj).2,(hB j hj).value]
  simpa only [he] using hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedHintPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.UseHintPackCallTiming`, which this module and modules that import it used -/

section

/-! ### `MlDsa.UseHintPackContract`, which only this module used -/

section

/-!
# ML-DSA: the contract of `UseHint`, packed

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- The fixed-gamma API retains the measured four-register ABI. -/
def useHintPackSig (g : Nat) : Sig where
  params := [("out", .array true .u8 (32*bitlen ((q-1)/(2*g)-1))),
    ("hints", .array false .u32 256), ("w", .array false .u32 256), ("gamma2", .int .u32 true)]

/-- Exact composition of FIPS 204 UseHint and SimpleBitPack. Every nonzero
hint word is interpreted as true, just as in the separate UseHint helper. -/
def useHintPackContract (g : Nat) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (useHintPackSig g).contract A
    (pre := fun _out _h w gamma m => gamma.toNat=g ∧ g∈gamma2s ∧ Reduced m w)
    (post := fun out h w _gamma m m' _ =>
      Spec.Sha3.bytesAt m' out (32*bitlen ((q-1)/(2*g)-1)) =
        simpleBitPack (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
          ((hintAt m h 1).headD (Vector.replicate n false)) (polyAt m w)) ((q-1)/(2*g)-1))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa

end

end

/-! ### `MlDsa.AArch64.Optimized.UseHintPackVerified`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open HighPack (packWidth)

def packSat (g : Nat) : State where
  gpr r := match r with | .x0=>0x1000 | .x1=>0x2000 | .x2=>0x3000 | .x3=>BitVec.ofNat 64 g | _=>0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000,1024⟩,⟨0x3000,1024⟩]
  wr := [⟨0x1000,32*packWidth g⟩]

/-- Fused UseHint and encoding against the architecture-independent shared specification. -/
theorem pack_verified {g : Nat} (hg : IsG g) :
    Verified AArch64.target Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      (useHintPackContract g AArch64.abi) := by
  refine Verified.of_correct (pack_correct hg) pack_ct ?_
  refine {pre:=?_,post:=?_,pub:=?_,sat:=?_}
  · rcases hg with rfl|rfl <;>
      (intro s h
       sig_pre [useHintPackContract,useHintPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs] at h
       sig_split h
       sig_reduce [packK,packWidth,arg32]
       exact ⟨by assumption,by assumption,by apply Region.Disjoint.symm; assumption,by apply Region.Disjoint.symm; assumption,by assumption,by assumption⟩)
  · intro s t hp hpost
    have hr : Reduced s.mem (s.gpr .x2) := by
      rcases hg with rfl|rfl <;>
        (sig_pre [useHintPackContract,useHintPackSig,AArch64.abi,AArch64.argRegs] at hp
         sig_split hp
         exact hp)
    have hs := packed_spec hg (h:=s.gpr .x1) hr
    rcases hg with rfl|rfl <;>
      (sig_post [useHintPackContract,useHintPackSig,packK,packWidth,AArch64.abi,AArch64.argRegs]
       exact hpost.trans hs)
  · rcases hg with rfl|rfl <;>
      sig_implies_pub [useHintPackContract,useHintPackSig,packK,AArch64.abi,AArch64.argRegs]
  · refine ⟨packSat g,?_⟩
    rcases hg with rfl|rfl <;>
      sig_pre [useHintPackContract,useHintPackSig,AArch64.abi,AArch64.argRegs] <;> sig_and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | exact fun i _=>by rw [VG.Proof.MlDsa.AArch64.Pack.coeffAt_zero];decide
      | decide

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end


/-! ## From `UseHintPackCall.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.UseHintPack (prog)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem callee (S : Nat) {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) : CalleeOk S prog (useHintPackContract g abi) :=
  CalleeOk.of_ct (pack_verified hg).1 (pack_verified hg).2.1 (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev args (out a b : Ptr) (g : Nat) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b),(.x3,.imm g)]

abbrev packLen (g : Nat) := 32*bitlen ((q-1)/(2*g)-1)

structure CallReady (out a b : Ptr) (g : Nat) (s : State) : Prop where
  outFit : (pa s out).toNat+packLen g≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  outA : (⟨pa s out,packLen g⟩ : Region).Disjoint (polyRegion (pa s a))
  outB : (⟨pa s out,packLen g⟩ : Region).Disjoint (polyRegion (pa s b))
  gamma : VG.Proof.MlDsa.AArch64.Round.IsG g
  canonical : Reduced s.mem (pa s b)
  readable : Covers [polyRegion (pa s a),polyRegion (pa s b),⟨pa s out,packLen g⟩] (s.rd++s.wr)
  writable : Covers [⟨pa s out,packLen g⟩] s.wr

theorem at_pre {s s1 : State} {out a b : Ptr} {g : Nat}
    (h : CallReady out a b g s) (h1 : Args (args out a b g) s s1) :
    (useHintPackContract g abi).pre
      (s1.callEntry.withRegions [polyRegion (pa s a),polyRegion (pa s b)] [⟨pa s out,packLen g⟩]) := by
  sig_pre [useHintPackContract,useHintPackSig,abi,argRegs]
  simp only [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,Args.mem h1,Arg.val]
  have hg : ((BitVec.ofNat 64 g).setWidth 32).toNat=g := by
    rcases h.gamma with rfl|rfl <;> decide
  rw [hg]
  exact ⟨trivial,trivial,h.outA,h.outB,h.outFit,h.aFit,h.bFit,rfl,
    VG.Proof.MlDsa.AArch64.Round.mem_of_isG h.gamma,h.canonical⟩

theorem args_ok {out a b : Ptr} {g : Nat}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) :
    ∀x∈args out a b g,x.2.Ok ∧ x.1∈argRegs := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩
  · exact ⟨trivial,by simp⟩

theorem at_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {out a b : Ptr} {g : Nat}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    (h : CallReady out a b g s) :
    WP isa (callAt nm prog (args out a b g)) s fun t =>
      VG.Proof.MlDsa.AArch64.Post S s t [⟨pa s out,packLen g⟩] ∧
      Spec.Sha3.bytesAt t.mem (pa s out) (packLen g)=
        simpleBitPack (Vector.zipWith (fun hj wj=>(useHint g hj wj).toNat)
          ((hintAt s.mem (pa s a) 1).headD (Vector.replicate n false)) (polyAt s.mem (pa s b)))
          ((q-1)/(2*g)-1) := by
  refine WP.mono (callAtSyms_ok hS (callee S h.gamma) (args_ok ho ha hb) (by simp)
    (fun s1 h1 _=>at_pre h h1) h.readable h.writable) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [useHintPackContract,useHintPackSig,abi,argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

/-! ## From `UseHintPackCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.UseHintPack (prog)
open VG.Proof.MlDsa.Arith (polyRegion)

theorem at_tr {S : Nat} {nm : String} {out a b : Ptr} {g : Nat} (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok)
    {Q : State → State → Prop}
    (hQ : ∀x z,Q x z → CallReady out a b g x ∧ CallReady out a b g z ∧
      pa x out=pa z out ∧ pa x a=pa z a ∧ pa x b=pa z b ∧ x.sp=z.sp) :
    RelCT isa Q (callAt nm prog (args out a b g)) fun _ _=>True := by
  refine callAtSyms_tr (callee S hg) (args_ok ho ha hb) (by simp)
    fun x z x1 z1 hp h1 h2 _ _ => ?_
  obtain ⟨rx,rz,eo,ea,eb,esp⟩ := hQ x z hp
  refine ⟨[polyRegion (pa x a),polyRegion (pa x b)],[⟨pa x out,packLen g⟩],
    at_pre rx h1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ea,eb]; exact at_pre rz h2
  · sig_pub [useHintPackContract,useHintPackSig,abi,argRegs]
    rw [Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.r2 h1,Args.r2 h2,Args.r3 h1,Args.r3 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,eo,ea,eb,rfl⟩
  · rw [eo,ea,eb]; exact rz.readable
  · rw [eo]; exact rz.writable
end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (wRow w1Row)

theorem hintPack_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.hintPack p r) s (SC p S σ h A' c0 q p.ℓ true (r+1)) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hrow : w1Len p*r+w1Len p≤p.k*w1Len p := by
    rw [←Nat.mul_succ,Nat.mul_comm p.k];exact Nat.mul_le_mul_left _ hr
  have hkw:=hF.w1
  have ro : inB (vR p++vW p) (rowP p r) (w1Len p)=true := by
    rcases hF.wl with he|he <;> vlay [he]
  have ra : inB (vR p++vW p) (hP p r) 1024=true := by vlayd
  have rb : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have wo : inB (vW p) (rowP p r) (w1Len p)=true := by
    rcases hF.wl with he|he <;> vlay [he]
  have plen : UseHintPack.packLen p.γ₂=w1Len p := rfl
  have ready : UseHintPack.CallReady (rowP p r) (hP p r) (wP p) p.γ₂ s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,
      L.disj (by rw [plen];rcases hF.wl with he|he <;> vlay [he]),
      L.disj (by rw [plen];rcases hF.wl with he|he <;> vlay [he]),
      Round.isG_of_mem hF.g2.1,hw.1,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  refine WP.mono_syms (UseHintPack.at_ok L.s64 (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(rowP p r,w1Len p)] := hp'.b
  have ht := hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hp'.cs .x24 (by decide) (by decide))
  refine ⟨ht.vc,ht.roots,ht.hh,ht.hint,ht.nok,ht.gd,ht.a,ht.z,ht.c,fun j hj=>?_,ht.x24⟩
  rcases (by omega_using [hj] : j<r∨j=r) with hj'|rfl
  · exact ht.rows j hj'
  · rw [hb.pa (L.ptrBs ro)]
    rw [hintRow_pa p s j,Proof.MlDsa.Verify.hintAt_row hs.hint hr,hw.2] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

/-! ### `MlDsa.AArch64.Verify.OptimizedRowEnd`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.InverseSingleCall`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

/-- Internal call contract for the same verified kernel. Its execution never
accesses the unused scratch argument of the separately emitted public helper. -/
theorem inverseSingle_callee (S : Nat) : CalleeOk S staticCode inverseK :=
  CalleeOk.of_ct inverse_correct inverse_ct (by lit_decide) (fun _ _ h => h) (Nat.zero_le _)

abbrev inverseSingleArgs (f : Ptr) : List (Reg × Arg) := [(.x0,.ptr f)]

structure InverseSingleReady (f : Ptr) (s : State) : Prop where
  held : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED")
  apart : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (pa s f))
  reduced : Reduced s.mem (pa s f)
  readable : Covers [tableRegion (s.syms "VG_MLDSA_INV_FOLDED"),outputRegion (pa s f)] (s.rd++s.wr)
  writable : Covers [outputRegion (pa s f)] s.wr

theorem inverseSingle_pre {s s1 : State} {f : Ptr}
    (h : InverseSingleReady f s) (h1 : Args (inverseSingleArgs f) s s1)
    (hy : s1.syms=s.syms) :
    inverseK.pre (s1.callEntry.withRegions [tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
      [outputRegion (pa s f)]) := by
  change tableRegion (s1.syms "VG_MLDSA_INV_FOLDED") ∈
      [tableRegion (s.syms "VG_MLDSA_INV_FOLDED"),outputRegion (pa s f)] ∧
    outputRegion (s1.callEntry.gpr .x0) ∈ [outputRegion (pa s f)] ∧
    (tableRegion (s1.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s1.callEntry.gpr .x0)) ∧
    InverseTable.Artifact s1.mem (s1.syms "VG_MLDSA_INV_FOLDED") ∧
    Reduced s1.mem (s1.callEntry.gpr .x0)
  rw [show s1.callEntry.gpr .x0=s1.gpr .x0 from rfl,Args.r0 h1,Args.mem h1,hy]
  exact ⟨by simp,by exact List.mem_singleton.mpr rfl,h.apart,h.held,h.reduced⟩

theorem inverseSingleArgs_ok {f : Ptr} (hf : (Arg.ptr f).Ok) :
    ∀x∈inverseSingleArgs f,x.2.Ok ∧ x.1∈argRegs := by
  intro x hx
  have he : x=(.x0,.ptr f) := by simpa only [inverseSingleArgs,List.mem_singleton] using hx
  subst x
  exact ⟨hf,by simp⟩

theorem inverseSingleAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {f : Ptr}
    (hf : (Arg.ptr f).Ok) (h : InverseSingleReady f s) :
    WP isa (callAt nm staticCode (inverseSingleArgs f)) s fun t =>
      Post S s t [outputRegion (pa s f)] ∧
      PolyIs t.mem (pa s f) (montgomeryNttInv (polyAt s.mem (pa s f))) := by
  refine WP.mono (callAtSyms_ok hS (inverseSingle_callee S) (inverseSingleArgs_ok hf) (by simp)
    (fun s1 h1 hy=>inverseSingle_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  change PolyIs t.mem (s1.callEntry.gpr .x0)
    (montgomeryNttInv (polyAt s1.mem (s1.callEntry.gpr .x0))) at hq
  rw [show s1.callEntry.gpr .x0=s1.gpr .x0 from rfl,Args.r0 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Arith.Montgomery

abbrev Diff (p : Params) (σ : State) (A' : Nat→Nat→Poly) (c0 : Poly) (r : Nat) : Poly :=
  sub (rDot p σ A' r) (multiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))

theorem subtract_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PolyIs s.mem (pa s (tm2P p))
      (montgomeryMultiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.subtract p) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r)) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : accChk (vR p) (vW p) (wP p) (tm2P p)=true := by unfold accChk;vlay
  have C : CalleeOk S (Impl.MlDsa.AArch64.Optimized.AddSub.code true) (subContract abi S) :=
    CalleeOk.of_verified L.s64 AddSub.sub_verified (Nat.zero_le _) (by change 0≤S;omega_using []) (by lit_decide)
  refine WP.mono_syms (accAt_ok L.s64 C L hc hw.1 ht.1) fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;vlay) h24,?_⟩
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  rw [hw.2,ht.2] at hv
  rw [Diff,scale_sub]
  exact hv

theorem inverse_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r))) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.inverse (wP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) (Proof.MlDsa.Verify.wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have wr : inB (vW p) (wP p) 1024=true := by vlayd
  have held : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") := by
    intro j hj
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (hs.roots.inverse.held j hj).trans (eq _ _ (by rw [InverseTable.expandedWords_length];exact hj))
  have ready : Inverse.InverseSingleReady (wP p) s :=
    ⟨held,hs.roots.inverse.apart_write (L.inW wr),hw.1,
      Covers.cons hs.roots.inverse.readable (L.cR rd),L.cW wr⟩
  refine WP.mono_syms (Inverse.inverseSingleAt_ok L.s64 (ptr_ok (L.ptrBs rd)) ready)
    fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(wP p,1024)] := hp'.b
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wr)
    (hp'.cs .x24 (by decide) (by decide)),?_⟩
  rw [hb.pa (L.ptrBs rd)]
  rw [hw.2,inv_cancel] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

end

-- separate module: keeps cached-row contracts independent of the private verification composition that consumes them.

@[expose] public section

/-! ## VerifyCopy -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

abbrev PublicCache (p : Params) (S : Nat) (σ s : State) : Prop :=
  ReadCache p.k S (fun r => VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) s

theorem copy_public_optimized {p : Params} (hF : VFacts p) {S : Nat} {σ s : State}
    (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (hw : Verify.Optimized.W p σ A r s) (cache : PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true r t ∧
      Verify.Optimized.W p σ A r t ∧ PublicCache p S σ t ∧
      PosPolyIs t.mem (pa t (tmP p)) (VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  have L := hs.vc.lay hF hp
  have hk := hF.k
  have hl := hF.l
  have hkl := hF.kl
  have hsc := hF.scr
  have hwrite : inB (vW p) (tmP p) 1024 = true := by vlayd
  refine WP.mono_syms (cache.copy_poly (show Reg.x28 ∈ keptRegs by decide)
    (L.inW hwrite) hr) fun t ⟨ht, h24, hc, hpoly⟩ hy => ?_
  refine ⟨hs.keep hF hp ht (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hw' => by obtain rfl := List.mem_singleton.mp hw'; exact hwrite) h24,
    L.keepPoly ht (by vlayd) hw, hc, PosPolyIs.of_canonical hpoly⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## VerifyKeyRow -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

theorem keyRow_optimized
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (hw : Verify.Optimized.W p σ A r s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow P p r) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true r t ∧
      Verify.Optimized.W p σ A r t ∧
      PosPolyIs t.mem (pa t (tmP p)) (VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
  refine WP.ite (M := isa) (s.gpr .x22 != 0) rfl (fun hn => ?_) (fun _ => ?_)
  · exact WP.mono (copy_public_optimized hF hp hr hs hw (cache (bne_iff_ne.mp hn)))
      fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.2⟩
  · refine WP.seq (WP.mono (Verify.Optimized.unpack_ok hP hF hp hr hs hw)
      fun t ⟨ht, hw', hv⟩ => ?_)
    exact Verify.Optimized.nttT_ok hF hp hr ht hw' hv

theorem row_optimized
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hdot : 16 * (Impl.MlDsa.AArch64.Verify.Optimized.dot p r).aarch64Depth ≤ S)
    (hrow : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r).aarch64Depth ≤ S)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true (r + 1) t ∧
      (t.gpr .x22 ≠ 0 → PublicCache p S σ t) := by
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row P p r) s
      (Verify.Optimized.SC p S σ h A c0 q p.ℓ true (r + 1)) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.row
    refine WP.seq (WP.mono (WP.optionalCache (Verify.Optimized.dot_ok hF hp hr hs)
      cache hdot hP.s64
      (fun t ht => (ht.1.vc.top.cs .x21 (by decide)).trans (hs.vc.top.cs .x21 (by decide)).symm)
      (fun t ht => (ht.1.vc.top.cs .x22 (by decide)).trans (hs.vc.top.cs .x22 (by decide)).symm))
      fun t ⟨⟨ht, hw⟩, hc⟩ => ?_)
    refine WP.seq (WP.mono (keyRow_optimized hP hF hp hr ht hw hc)
      fun t ⟨ht, hw, hv⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.product_ok hF hp hr ht hw hv)
      fun t ⟨ht, hw, hv⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.subtract_ok hF hp hr ht hw hv)
      fun t ⟨ht, hw⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.inverse_ok hF hp hr ht hw)
      fun t ⟨ht, hw⟩ => ?_)
    exact Verify.Optimized.hintPack_ok hF hp hr ht hw
  exact WP.optionalCache main cache hrow hP.s64
    (fun t ht => (ht.vc.top.cs .x21 (by decide)).trans (hs.vc.top.cs .x21 (by decide)).symm)
    (fun t ht => (ht.vc.top.cs .x22 (by decide)).trans (hs.vc.top.cs .x22 (by decide)).symm)

/-- The verification core, with the static root tables of its transforms. -/
def verifyCoreK (p : Params) : Contract isa where
  pre s := vPre p 16 s ∧ Sign.StaticRoots 16 s ∧
    (s.gpr .x22 ≠ 0 → PublicCache p 16 s s)
  post := (verifyContract p abi 16).post
  pub x y := vPub p 16 x y ∧
    (x.syms "VG_MLDSA_NTT_EXPANDED" = y.syms "VG_MLDSA_NTT_EXPANDED" ∧
      x.syms "VG_MLDSA_INV_FOLDED" = y.syms "VG_MLDSA_INV_FOLDED") ∧ SameIn [.x21, .x22] x y

end VG.Proof.MlDsa.AArch64.PreparedKey
