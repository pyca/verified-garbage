module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlKem.Arith
import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Data.Fintype.Fin
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalLoad
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish

/-! ### `MlDsa.AArch64.Optimized.ResponseHintFinish`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Packed hint count and norm-success bit, exactly as returned to the signer. -/
def hintFinishValue (counts failures : BitVec 128) : BitVec 64 :=
  (vword counts 0+vword counts 1+vword counts 2+vword counts 3).setWidth 64 |||
    (finishValue failures <<< 32)

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedCheckSource`, which the modules that import this one used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedLowLane`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedReduce`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (reduceWord normMask minMask)

/-- Register-parametric form used by the two interleaved final r0 lanes. -/
def reduceRegs (a t : VReg) : List Instr :=
 [.vop (.add .s4 t a .v8),.vop (.shift .sshr .s4 t t 23),.vop (.mls a t .v31)]

def normRegs (a t : VReg) : List Instr :=
 [.vop (.add .s4 t a .v9),.vop (.umin t t .v10),
  .vop (.cmeq .s4 t t .v10),.vop (.logic .orr .v30 .v30 t)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end


/-! ## `PairedLowVec` -/

@[expose] public section

/-- `∀ r ∈ l, r ∈ l'` for lists of registers written out: by one simp, else by `grind`. -/
tactic_template "paired_regs_sub" : tactic => `(tactic| first
  | (simp (config := { contextual := true }) only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, true_or, or_true, and_true, implies_true, and_self, forall_eq_or_imp, forall_eq,
      eq_self_iff_true]; done)
  | (intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at *; grind only))

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- Signed correction with the exact registers used by each pipelined lane. -/
def lowCadd (a t : VReg) : List Instr :=
 [.vop (.shift .sshr .s4 t a 31),.vop (.logic .and t t .v31),.vop (.add .s4 a a t)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowWord` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (raw highWord)

def lowHighWord (g : Nat) (a : BitVec 32) : BitVec 32 :=
  if g==261888 then raw g a &&& 15#32 else highWord g a

theorem lowHighWord_eq {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) : lowHighWord g a=highWord g a := by
  unfold lowHighWord
  split
  · rename_i h
    have he : g=261888 := by simpa using h
    subst g
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and,show (15#32).toNat=2^4-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod,HighPack.raw_toNat hg ha,HighPack.highWord_toNat hg ha]
    rfl
  · rfl

/-- The selected lane uses reduce32 after high-bit subtraction. It gives the
same small signed low part as the reference's centered correction. -/
theorem lowReduced_spec {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<VG.Spec.MlDsa.q) :
    (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))).toInt=
      VG.Spec.MlDsa.lowBits g ⟨a.toNat,ha⟩ := by
  rw [lowHighWord_eq hg ha]
  have hhigh := HighPack.highWord_toNat hg ha
  have hraw : (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt=
      (a.toNat:Int)-(hbF g a.toNat%hbM g)*(2*g) := by
    have ht := BitVec.toInt_eq_toNat_cond (a-highWord g a*BitVec.ofNat 32 (2*g))
    simp only [BitVec.toNat_sub,BitVec.toNat_mul,BitVec.toNat_ofNat] at ht
    rw [hhigh] at ht
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega_using [ha, ht]
  have hb : -8380417<(a-highWord g a*BitVec.ofNat 32 (2*g)).toInt ∧
      (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt<8380417 := by
    rw [hraw]
    have hr : a.toNat<8380417 := ha
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega_using [ha]
  have hreduce := Response.reduceWord_int (a-highWord g a*BitVec.ofNat 32 (2*g)) (by omega_using [hb]) (by omega_using [hb])
  rw [hreduce]
  have hrange := reduce32_bounds (x := (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt) (by omega_using [hb]) (by omega_using [hb])
  have hmod := reduce32_mod (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt
  have hlow := Response.lowBits_centered hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hlrange := Response.lowBits_bounds hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hgsmall : g≤261888 := by rcases hg with rfl | rfl <;> decide
  change Spec.MlDsa.lowBits g ⟨a.toNat,ha⟩ = _ at hlow
  rw [← hraw] at hlow
  split at hlow <;> omega_using [hrange, hmod, hlrange, hgsmall, hlow]

theorem lowReduced_eq {g : Nat} (hg : IsG g) {a : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) :
    Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))=
      Response.lowWord a (HighPack.highWord g a) (BitVec.ofNat 32 (2*g)) := by
  apply BitVec.eq_of_toInt_eq
  rw [lowReduced_spec hg ha,Response.lowWord_spec hg ha]

/-- Semantic low part of the exact signed product-subtraction pipeline. -/
theorem subLowReduced_spec {g : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    let c := Inverse.signCorrected (Response.reduceWord (a-b))
    (Response.reduceWord (c-lowHighWord g c*BitVec.ofNat 32 (2*g))).toInt=
      Spec.MlDsa.lowBits g (Spec.MlDsa.ofInt ((a.toNat:Int)-b.toInt)) := by
  dsimp only
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (Spec.MlDsa.ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowReduced_eq hg cb]
  exact Response.subLow_word hg ha bl bh
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowHigh` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (raw)
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def lowHf (g : Nat) (d a : VReg) : List Instr :=
 [.vop (.add .s4 d a .v11),.vop (.shift .ushr .s4 d d 7),
 .vop (.mul d d .v12),.vop (.add .s4 d d .v13),.vop (.shift .ushr .s4 d d (dShift g))]


end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowInput` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

def lowInputWord (s : State) (raw : VReg) (off e : Nat) : BitVec 32 :=
 Inverse.signCorrected (Response.reduceWord
  (vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e-vword (s.v raw) e))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowReduce2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

def reduceTwo (a t b u : VReg) : List Instr :=
 ((reduceRegs a t).zip (reduceRegs b u)).flatMap fun (x,y) => [x,y]

/-- The two reductions execute in the measured alternating instruction order. -/
theorem reduceTwo_ok {a t b u : VReg}
    (hat : a≠t) (hab : a≠b) (hau : a≠u) (htb : t≠b) (htu : t≠u) (hbu : b≠u)
    (hregs : ∀r∈[a,t,b,u],r≠.v8 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀v,VChg [a,t,b,u] s v →
      (∀e<4,vword (v.v a) e=Response.reduceWord (vword (s.v a) e)) →
      (∀e<4,vword (v.v b) e=Response.reduceWord (vword (s.v b) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (reduceTwo a t b u++rest)) s Q := by
  refine wp_vop (d := t) rfl fun s1 h1 => wp_vop (d := u) rfl fun s2 h2 =>
    wp_vop (d := t) rfl fun s3 h3 => wp_vop (d := u) rfl fun s4 h4 =>
    wp_vop (d := a) rfl fun s5 h5 => wp_vop (d := b) rfl fun s6 h6 => ?_
  have hqT := Ne.symm (hregs t (by simp)).2
  have hqU := Ne.symm (hregs u (by simp)).2
  have hqA := Ne.symm (hregs a (by simp)).2
  have hcT := Ne.symm (hregs t (by simp)).1
  refine k s6 (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg |>.mono ?_) ?_ ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [h6.get a hab,h5.v,vword_mapWords3 _ _ _ _ he,
      h4.get a hau,h3.get a hat,h2.get a hau,h1.get a hat,
      h4.get t htu,h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get t htu,h1.v,VG.AArch64.vword_map2 _ _ _ he,
      h4.get .v31 hqU,h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he,hc e he]
    rfl
  · intro e he
    rw [h6.v,vword_mapWords3 _ _ _ _ he,
      h5.get b (Ne.symm hab),h4.get b hbu,h3.get b (Ne.symm htb),h2.get b hbu,h1.get b (Ne.symm htb),
      h5.get u (Ne.symm hau),h4.v,VG.AArch64.vword_map2 _ _ _ he,
      h3.get u (Ne.symm htu),h2.v,VG.AArch64.vword_map2 _ _ _ he,
      h1.get b (Ne.symm htb),h1.get .v8 hcT,
      h5.get .v31 hqA,h4.get .v31 hqU,h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he,hc e he]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCadd2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

def caddTwo (a t b u : VReg) : List Instr :=
 ((lowCadd a t).zip (lowCadd b u)).flatMap fun (x,y) => [x,y]

/-- The two signed corrections execute in the measured alternating instruction order. -/
theorem caddTwo_ok {a t b u : VReg}
    (hat : a≠t) (hab : a≠b) (hau : a≠u) (htb : t≠b) (htu : t≠u) (hbu : b≠u)
    (hregs : ∀r∈[a,t,b,u],r≠.v8 ∧ r≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀v,VChg [a,t,b,u] s v →
      (∀e<4,vword (v.v a) e=Inverse.signCorrected (vword (s.v a) e)) →
      (∀e<4,vword (v.v b) e=Inverse.signCorrected (vword (s.v b) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (caddTwo a t b u++rest)) s Q := by
  refine wp_vop (d := t) rfl fun s1 h1 => wp_vop (d := u) rfl fun s2 h2 =>
    wp_vop (d := t) rfl fun s3 h3 => wp_vop (d := u) rfl fun s4 h4 =>
    wp_vop (d := a) rfl fun s5 h5 => wp_vop (d := b) rfl fun s6 h6 => ?_
  have hqT := Ne.symm (hregs t (by simp)).2
  have hqU := Ne.symm (hregs u (by simp)).2
  refine k s6 (((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).trans h5.chg).trans h6.chg |>.mono ?_) ?_ ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [h6.get a hab,h5.v,VG.AArch64.vword_map2 _ _ _ he,
      h4.get a hau,h3.get a hat,h2.get a hau,h1.get a hat,
      h4.get t htu,h3.v,Inverse.word_and,
      h2.get t htu,h1.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v31 hqU,h1.get .v31 hqT,hq e he]
    rfl
  · intro e he
    rw [h6.v,VG.AArch64.vword_map2 _ _ _ he,
      h5.get b (Ne.symm hab),h4.get b hbu,h3.get b (Ne.symm htb),h2.get b hbu,h1.get b (Ne.symm htb),
      h5.get u (Ne.symm hau),h4.v,Inverse.word_and,
      h3.get u (Ne.symm htu),h2.v,VG.AArch64.vword_map2 _ _ _ he,
      h1.get b (Ne.symm htb),
      h3.get .v31 hqT,h2.get .v31 hqU,h1.get .v31 hqT,hq e he]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLoad2` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq)

def lowLoadTwo (r q : VReg) (off : Nat) : List Instr :=
 [.ldrq .v27 .x15 off,.ldrq .v29 .x15 (off+128),
  .vop (.sub .s4 .v24 .v27 r),.vop (.sub .s4 r .v29 q)]

/-- Consume the first raw register before the second lane reuses it. -/
theorem lowLoadTwo_ok {r q : VReg} {off : Nat}
    (hr24 : r≠.v24) (hr27 : r≠.v27) (hr29 : r≠.v29)
    (hq24 : q≠.v24) (hq27 : q≠.v27) (hq29 : q≠.v29)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (hread : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hread' : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (k : ∀v,VChg [.v27,.v29,.v24,r] s v →
      (∀e<4,vword (v.v .v24) e=
        vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e-vword (s.v r) e) →
      (∀e<4,vword (v.v r) e=
        vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16) e-vword (s.v q) e) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowLoadTwo r q off++rest)) s Q := by
  refine wp_ldrq (by omega_using [ho]) rfl hread fun s1 h1 => ?_
  refine wp_ldrq (by omega_using [ho]) rfl (by rw [h1.rd,h1.wr,h1.gpr]; exact hread') fun s2 h2 => ?_
  refine wp_vop (d := .v24) rfl fun s3 h3 => wp_vop (d := r) rfl fun s4 h4 => ?_
  refine k s4 ((((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono (by simp)) ?_ ?_
  · intro e he
    rw [h4.get .v24 (Ne.symm hr24),h3.v,VG.AArch64.vword_map2 _ _ _ he,
      h2.get .v27 (by decide),h1.v,h2.get r hr29,h1.get r hr27]
  · intro e he
    rw [h4.v,VG.AArch64.vword_map2 _ _ _ he,h3.get .v29 (by decide),h2.v,
      h1.mem,h1.gpr,h3.get q hq24,h2.get q hq29,h1.get q hq27]
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedProductField`, which this module and modules that import it used -/

section

/-! ## From `PairedFirstSource.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The paired scratch writes cannot alter later challenge/source slices. -/
theorem valuesAt_frame_slice {m m' : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (hf : Frame [⟨p,2048⟩] m m')
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) :
    valuesAt m' (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u))=
      valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) := by
  funext poly
  apply Vector.ext
  intro j hj
  have ra : m'.read (a+BitVec.ofNat 64 (128*u+16*j)) 16=
      m.read (a+BitVec.ofNat 64 (128*u+16*j)) 16 :=
    hf.read (Offset.contains_base a (by omega_using [hu, hj] : 128*u+16*j+16≤1024) (by omega_using [hu, hj]))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ha) (by decide)
  have rb : m'.read (b+BitVec.ofNat 64 (128*u+(1024*poly.val+16*j))) 16=
      m.read (b+BitVec.ofNat 64 (128*u+(1024*poly.val+16*j))) 16 :=
    hf.read (Offset.contains_base b (by omega_using [hu, hj] : 128*u+(1024*poly.val+16*j)+16≤2048) (by omega_using [hu, hj]))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hb) (by decide)
  simp only [valuesAt,Vector.getElem_ofFn,BitVec.add_assoc,←BitVec.ofNat_add,ra,rb]

/-- The machine memory recursion reads the same products as the original inputs. -/
theorem firstPass_valuesAt {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) :
    valuesAt (firstPassMem m p a b u) (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u))=
      valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) :=
  valuesAt_frame_slice hu (firstPass_frame (by omega_using [hu])) ha hb
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedStoreRead.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def storeValues {α : Type} (xs : List α) (addr : α → Addr) (values : α → BitVec 128) (m : Mem) : Mem :=
 xs.foldl (fun m i => m.write (addr i) 16 (values i)) m

theorem storeValues_read_other {α : Type} (xs : List α) (addr : α → Addr)
    (values : α → BitVec 128) (m : Mem) (a : Addr)
    (hs : ∀i∈xs,Mem.Sep a 16 (addr i) 16) :
    (storeValues xs addr values m).read a 16=m.read a 16 := by
  induction xs generalizing m with
  | nil => rfl
  | cons i xs ih =>
    change (storeValues xs addr values (m.write (addr i) 16 (values i))).read a 16=_
    rw [ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj)),Mem.read_write_sep (hs i (by simp)) (by decide)]

theorem storeValues_read_slot {α : Type} [DecidableEq α] (xs : List α) (addr : α → Addr)
    (values : α → BitVec 128) (m : Mem) (i : α) (hi : i∈xs)
    (hs : ∀j∈xs,j≠i → Mem.Sep (addr i) 16 (addr j) 16) :
    (storeValues xs addr values m).read (addr i) 16=values i := by
  induction xs generalizing m with
  | nil => simp at hi
  | cons j xs ih =>
    change (storeValues xs addr values (m.write (addr j) 16 (values j))).read _ 16=_
    by_cases ht : i∈xs
    · exact ih _ ht (fun k hk => hs k (List.mem_cons_of_mem _ hk))
    · have he : i=j := (List.mem_cons.mp hi).resolve_right ht
      subst j
      rw [storeValues_read_other _ _ _ _ _ (fun k hk => hs k (List.mem_cons_of_mem _ hk)
        (by intro he; subst k; exact ht hk))]
      simpa only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] using
        Mem.readW_writeW_self m (addr i) 16 (values i) (by decide)

def pairIndices : List (Fin 2 × Fin 8) :=
 (List.finRange 2).flatMap fun p => (List.finRange 8).map fun j => (p,j)

theorem pairIndices_mem (i : Fin 2 × Fin 8) : i∈pairIndices := by
  simp only [pairIndices,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  exact ⟨i.1,i.2,rfl⟩

theorem writePair_values (v : Values) (base : Addr) (stride : Nat) (m : Mem) :
    writePair v base stride m=storeValues pairIndices
      (fun i => base+BitVec.ofNat 64 (1024*i.1.val+stride*i.2.val))
      (fun i => (v i.1)[i.2.val]) m := by
  simp only [writePair,storeValues,pairIndices,List.foldl_flatMap,List.foldl_map]

theorem pair16_sep (base : Addr) {i j : Fin 2 × Fin 8} (hne : j≠i) :
    Mem.Sep (base+BitVec.ofNat 64 (1024*i.1.val+16*i.2.val)) 16
      (base+BitVec.ofNat 64 (1024*j.1.val+16*j.2.val)) 16 := by
  have hd : j.1.val≠i.1.val ∨ j.2.val≠i.2.val := by
    by_contra h
    simp only [not_or,Classical.not_not] at h
    exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  exact Offset.sep base (by omega_using [hd]) (by omega_using []) (by omega_using [])

/-- Each stored 16-byte first-pass vector is recovered exactly from its own bank. -/
theorem writePair_read16 (v : Values) (base : Addr) (m : Mem) (p : Fin 2) (j : Fin 8) :
    (writePair v base 16 m).read (base+BitVec.ofNat 64 (1024*p.val+16*j.val)) 16=(v p)[j.val] := by
  rw [writePair_values]
  exact storeValues_read_slot _ _ _ _ (p,j) (pairIndices_mem _) (fun _ _ hn => pair16_sep base hn)
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirstRead.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem writePair_slice_other (v : Values) (base : Addr) (m : Mem)
    {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u) (poly : Fin 2) (j : Fin 8) :
    (writePair v (base+BitVec.ofNat 64 (128*u)) 16 m).read
      ((base+BitVec.ofNat 64 (128*k))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16=
    m.read ((base+BitVec.ofNat 64 (128*k))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16 := by
  rw [writePair_values]
  apply storeValues_read_other
  intro i _
  simp only [BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep base (by omega_using [hu, hk, hne]) (by omega_using [hk]) (by omega_using [hu])

/-- Every completed local slice contains the original-input product followed by
exactly the first five inverse layers, independent of later scratch writes. -/
theorem firstPass_read_written {m : Mem} {p a b : Addr} {n u : Nat}
    (hn : n≤8) (hu : u<n)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) (j : Fin 8) :
    (firstPassMem m p a b n).read
      ((p+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16=
    (Inverse.fiveValues u (valuesAt m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) poly))[j.val] := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : u=n
    · subst u
      rw [firstPassMem,writePair_read16,firstPass_valuesAt (by omega_using [hn]) ha hb]
    · rw [firstPassMem,writePair_slice_other _ _ _ (by omega_using [hn]) (by omega_using [hn, hu]) he]
      exact ih (by omega_using [hn]) (by omega_using [hu, he])
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFinalSource.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The final strided bank is the transpose of the eight completed local slices. -/
theorem firstPass_finalBank {m : Mem} {p a b : Addr} {u : Nat} (hu : u<8)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) :
    readPair (firstPassMem m p a b 8) (p+BitVec.ofNat 64 (16*u)) 128 poly=
      Vector.ofFn (fun j : Fin 8 =>
        (Inverse.fiveValues j.val (valuesAt m (a+BitVec.ofNat 64 (128*j.val))
          (b+BitVec.ofNat 64 (128*j.val)) poly))[u]) := by
  apply Vector.ext
  intro j hj
  simp only [readPair,Vector.getElem_ofFn]
  have had : (p+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (1024*poly.val+128*j)=
      (p+BitVec.ofNat 64 (128*j))+BitVec.ofNat 64 (1024*poly.val+16*u) := by
    simp only [BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 16*u+(1024*poly.val+128*j)=128*j+(1024*poly.val+16*u) by omega_using []]
  rw [had]
  exact firstPass_read_written (by decide) hj ha hb poly ⟨u,hu⟩

/-- Final-pass output stores outside work preserve every strided inverse bank. -/
theorem readPair_workFrame {m m' : Mem} {p : Addr} {u : Nat} {W : List Region}
    (hu : u<8) (hf : Frame W m m')
    (hd : ∀r∈W,(⟨p,2048⟩ : Region).Disjoint r) :
    readPair m' (p+BitVec.ofNat 64 (16*u)) 128=readPair m (p+BitVec.ofNat 64 (16*u)) 128 := by
  funext poly
  apply Vector.ext
  intro j hj
  simp only [readPair,Vector.getElem_ofFn,BitVec.add_assoc,←BitVec.ofNat_add]
  exact hf.read (Offset.contains_base p (by omega_using [hu, hj] : 16*u+(1024*poly.val+128*j)+16≤2048) (by omega_using [hu, hj])) hd (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedProductField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

theorem valuesAt_word (m : Mem) (a b : Addr) (poly : Fin 2) (j : Fin 8) {e : Nat} (he : e<4) :
    vword ((valuesAt m a b poly)[j.val]) e=centeredProduct
      (vword (m.read (a+BitVec.ofNat 64 (16*j.val)) 16) e)
      (vword (m.read (b+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16) e) := by
  simp only [valuesAt,Vector.getElem_ofFn]
  rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> simp only [vword_ofVWords_0,vword_ofVWords_1,vword_ofVWords_2,vword_ofVWords_3]

/-- The paired SIMD layout contains the same pointwise products as the scalar polynomial view. -/
theorem valuesAt_coeff (m : Mem) (a b : Addr) (u : Nat) (poly : Fin 2) (j : Fin 8)
    {e : Nat} (he : e<4) :
    vword ((valuesAt m (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u)) poly)[j.val]) e=
      centeredProduct (coeffAt m a (32*u+4*j.val+e))
        (coeffAt m (b+BitVec.ofNat 64 (1024*poly.val)) (32*u+4*j.val+e)) := by
  rw [valuesAt_word _ _ _ _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [coeffAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 128*u+16*j.val+4*e=4*(32*u+4*j.val+e) by omega_using [],
    show 128*u+(1024*poly.val+16*j.val)+4*e=1024*poly.val+4*(32*u+4*j.val+e) by omega_using []]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedLowRun`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedCallFrame`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure CallFrame (gr : List Reg) (vr : List VReg) (s t : State) : Prop where
  gpr : ∀r,r∉gr → t.gpr r=s.gpr r
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  vec : ∀r,r∉vr → t.v r=s.v r

theorem CallFrame.ofStep {vr : List VReg} {s t : State} (h : StepFrame vr s t) : CallFrame [] vr s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp,h.vec⟩
theorem CallFrame.ofKeep {gr : List Reg} {s t : State} (h : Keep gr s t) (hv : t.v=s.v) : CallFrame gr [] s t :=
  ⟨fun r hr => h.get r hr,h.rd,h.wr,h.sp,fun _ _ => congrFun hv _⟩
theorem CallFrame.trans {gr gs : List Reg} {vr vs : List VReg} {s t u : State}
    (h : CallFrame gr vr s t) (h' : CallFrame gs vs t u) : CallFrame (gr++gs) (vr++vs) s u := by
  refine ⟨?_,h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp,?_⟩
  · intro r hr
    rw [h'.gpr r (fun hm => hr (List.mem_append_right _ hm)),h.gpr r (fun hm => hr (List.mem_append_left _ hm))]
  · intro r hr
    rw [h'.vec r (fun hm => hr (List.mem_append_right _ hm)),h.vec r (fun hm => hr (List.mem_append_left _ hm))]
theorem CallFrame.mono {gr gs : List Reg} {vr vs : List VReg} {s t : State}
    (h : CallFrame gr vr s t) (hg : gr⊆gs) (hv : vr⊆vs) : CallFrame gs vs s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (hg hm)),h.rd,h.wr,h.sp,
    fun r hr => h.vec r (fun hm => hr (hv hm))⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedFinalAdvance`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def finalAdvance : List Instr :=
  [.addImm .x .x2 .x2 16,.addImm .x .x15 .x15 16,.addImm .x .x16 .x16 16,.subImm .x .x12 .x12 1]

theorem finalAdvance_ok (s : State) : WP isa (.block finalAdvance) s fun t =>
    ((t.gpr .x2=s.gpr .x2+16 ∧ t.gpr .x15=s.gpr .x15+16 ∧
      t.gpr .x16=s.gpr .x16+16 ∧ t.gpr .x12=s.gpr .x12-1 ∧ t.mem=s.mem) ∧
      Keep [.x2,.x12,.x15,.x16] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv:=rfl)
  unfold finalAdvance
  arun
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem final_z_eq (g : Nat) : VG.Impl.MlDsa.AArch64.Optimized.Paired.final .z g=
    finalCheckCode false++finalAdvance := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Paired.final finalCheckCode
  rw [finalPrefix_eq]
  have he : ([0,1].flatMap fun p => (List.range 8).flatMap fun j =>
      VG.Impl.MlDsa.AArch64.Optimized.Paired.check .z g p j)=checkRunCode false allChecks := by
    simp only [zCheck_eq]
    rfl
  rw [he]
  simp only [List.append_assoc]
  rfl

theorem final_h_eq (g : Nat) : VG.Impl.MlDsa.AArch64.Optimized.Paired.final .h g=
    finalCheckCode true++finalAdvance := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Paired.final finalCheckCode
  rw [finalPrefix_eq]
  have he : ([0,1].flatMap fun p => (List.range 8).flatMap fun j =>
      VG.Impl.MlDsa.AArch64.Optimized.Paired.check .h g p j)=checkRunCode true allChecks := by
    simp only [hCheck_eq]
    decide +kernel
  rw [he]
  simp only [List.append_assoc]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

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

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Earlier z/h output writes leave the raw inverse source unchanged. -/
theorem finalPass_readPair (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u k : Nat} (hu : u≤8) (hk : k<8)
    (hd : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    readPair (finalPassData hint work out aux c d u).mem (work+BitVec.ofNat 64 (16*k)) 128 =
      readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 := by
  exact readPair_workFrame hk (finalPass_frame hint work out aux c d hu)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd)

/-- Earlier r0 writes to either output leave the raw inverse source unchanged. -/
theorem lowPass_readPair (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u k : Nat} (hu : u≤8) (hk : k<8)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    readPair (lowPassData g work out aux c d u).mem (work+BitVec.ofNat 64 (16*k)) 128 =
      readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 := by
  exact readPair_workFrame hk (lowPass_frame g work out aux c d hu)
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl <;> with_reducible assumption)

/-- Each z/h iteration uses the same original transform result. -/
theorem finalPass_step (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {u : Nat} (hu : u<8)
    (hd : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    finalPassData hint work out aux c d (u+1)=
      checkRun hint (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*u)) 128 p))
        (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c
        (finalPassData hint work out aux c d u) allChecks := by
  rw [finalPassData,finalPass_readPair hint work out aux c d (by omega_using [hu]) hu hd]

theorem lowPass_step (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u : Nat} (hu : u<8)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    lowPassData g work out aux c d (u+1)=
      lowRun g (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*u)) 128 p))
        (out+BitVec.ofNat 64 (16*u)) (aux+BitVec.ofNat 64 (16*u)) c
        (lowPassData g work out aux c d u) allLow := by
  rw [lowPassData,lowPass_readPair g work out aux c d (by omega_using [hu]) hu ho ha]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedFinish`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Optimized.Response (finishValue hintFinishValue exec_umov_word)

def returnCode (kind : Kind) : List Instr :=
 [.umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.logic .orr .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v30 3,
 .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1] ++
 (if kind==.h then [.lsl .x .x0 .x0 32,
 .umov .w .x9 .v14 0,.umov .w .x10 .v14 1,.add .w .x9 .x9 .x10,
 .umov .w .x10 .v14 2,.add .w .x9 .x9 .x10,.umov .w .x10 .v14 3,
 .add .w .x9 .x9 .x10,.logic .orr .x .x0 .x0 .x9] else [])
def restoreCode : List Instr := saved.zipIdx.map (fun (r,i) => .ldrq r .x2 (1920+16*i))

theorem finish_split (kind : Kind) : finish kind=returnCode kind++restoreCode := by
  cases kind <;> rfl

def returnValue (kind : Kind) (s : State) : BitVec 64 :=
  if kind==.h then hintFinishValue (s.v .v14) (s.v .v30) else finishValue (s.v .v30)

/-- Both polynomial norm flags are accumulated before returning. The hint
kernel returns the combined count in low32 and success in bit32. -/
theorem return_ok (kind : Kind) (s : State) :
    WP isa (.block (returnCode kind)) s fun t =>
      ((t.gpr .x0=returnValue kind s ∧ t.mem=s.mem) ∧ Keep [.x0,.x9,.x10] s t) ∧ t.v=s.v := by
  cases kind <;>
    apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl) <;>
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl) <;>
    unfold returnCode returnValue hintFinishValue finishValue <;>
    arun [exec_umov_word (i := 0) (hi := by decide),exec_umov_word (i := 1) (hi := by decide),
      exec_umov_word (i := 2) (hi := by decide),exec_umov_word (i := 3) (hi := by decide)]
  · rfl
  · rfl
  · exact BitVec.or_comm _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end


/-! ## From `PairedExtra.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def extraSlots (off : Nat) : List (VReg × Nat) :=
  saved.zipIdx.map fun (r,i) => (r,off+16*i)

theorem save_code : save=(extraSlots 2048).map (fun p => Instr.strq p.1 .x0 p.2) := rfl
theorem restore_code : restoreCode=(extraSlots 1920).map (fun p => Instr.ldrq p.1 .x2 p.2) := rfl

theorem save_ok {s : State}
    (hr : ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VMem s t (writeSlice (extraSlots 2048) (s.gpr .x0) s.v s.mem) →
      WP isa (.block rest) t Q) : WP isa (.block (save++rest)) s Q := by
  rw [save_code]
  exact store_many_ok _ _ (by decide) hr k

theorem restore_ok {s : State}
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg saved s t →
      (∀p∈extraSlots 1920,t.v p.1=s.mem.read (s.gpr .x2+BitVec.ofNat 64 p.2) 16) →
      WP isa (.block rest) t Q) : WP isa (.block (restoreCode++rest)) s Q := by
  rw [restore_code]
  exact load_many_ok _ _ (by decide) (by decide) hr k

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedSavedMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem read_write_self (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.write a 16 v).read a 16 = v := by
  simpa only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m a 16 v (by decide)

theorem writeSlice_read_other (xs : List (VReg × Nat)) (base a : Addr)
    (v : VReg → BitVec 128) (m : Mem)
    (hs : ∀ p∈xs,Mem.Sep a 16 (base+BitVec.ofNat 64 p.2) 16) :
    (writeSlice xs base v m).read a 16=m.read a 16 := by
  induction xs generalizing m with
  | nil => rfl
  | cons p xs ih =>
    change (writeSlice xs base v (m.write (base+BitVec.ofNat 64 p.2) 16 (v p.1))).read a 16=_
    rw [ih _ (fun q hq => hs q (List.mem_cons_of_mem _ hq)),
      Mem.read_write_sep (hs p (by simp)) (by decide)]

theorem writeSlice_read_slot (xs : List (VReg × Nat)) (base : Addr)
    (v : VReg → BitVec 128) (m : Mem) (p : VReg × Nat) (hp : p∈xs)
    (hs : ∀ q∈xs,q≠p → Mem.Sep (base+BitVec.ofNat 64 p.2) 16
      (base+BitVec.ofNat 64 q.2) 16) :
    (writeSlice xs base v m).read (base+BitVec.ofNat 64 p.2) 16=v p.1 := by
  induction xs generalizing m with
  | nil => simp at hp
  | cons q xs ih =>
    change (writeSlice xs base v (m.write (base+BitVec.ofNat 64 q.2) 16 (v q.1))).read _ 16=_
    by_cases ht : p∈xs
    · exact ih _ ht (fun r hr => hs r (List.mem_cons_of_mem _ hr))
    · have he : p=q := (List.mem_cons.mp hp).resolve_right ht
      subst q
      rw [writeSlice_read_other _ _ _ _ _ (fun r hr => hs r (List.mem_cons_of_mem _ hr)
        (by intro h; subst r; exact ht hr)),read_write_self]

theorem writeSlice_frame (xs : List (VReg × Nat)) (base : Addr)
    (v : VReg → BitVec 128) (m : Mem) (r : Region)
    (hc : ∀ p∈xs,r.Contains (base+BitVec.ofNat 64 p.2) 16) :
    Frame [r] m (writeSlice xs base v m) := by
  induction xs generalizing m with
  | nil => exact Frame.refl _ _
  | cons p xs ih =>
    change Frame [r] m (writeSlice xs base v (m.write (base+BitVec.ofNat 64 p.2) 16 (v p.1)))
    exact ((Frame.refl [r] m).write (List.mem_singleton_self _) _ (hc p (by simp))).trans
      (ih _ (fun q hq => hc q (List.mem_cons_of_mem _ hq)))

/-- An explicit index for each callee-saved vector. -/
def savedReg (i : Fin 8) : VReg := saved[i.val]!

theorem extraSlots_mem (off : Nat) (p : VReg × Nat) :
    p∈extraSlots off ↔ ∃ i : Fin 8,p=(savedReg i,off+16*i.val) := by
  have he : extraSlots off = (List.finRange 8).map (fun i => (savedReg i,off+16*i.val)) := rfl
  rw [he]
  simp only [List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨i,hi.symm⟩
  · rintro ⟨i,hi⟩; exact ⟨i,hi.symm⟩
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedSaved.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Saved full-width caller vectors at the end of the paired work buffer. -/
def Saved (m : Mem) (work : Addr) (v : VReg → BitVec 128) : Prop :=
  ∀ i : Fin 8,m.read (work+BitVec.ofNat 64 (2048+16*i.val)) 16=v (savedReg i)

theorem saved_after (m : Mem) (work : Addr) (v : VReg → BitVec 128) :
    Saved (writeSlice (extraSlots 2048) work v m) work v := by
  intro i
  refine writeSlice_read_slot _ _ _ _ (savedReg i,2048+16*i.val)
    ((extraSlots_mem _ _).mpr ⟨i,rfl⟩) ?_
  intro p hp hne
  obtain ⟨j,rfl⟩ := (extraSlots_mem _ _).mp hp
  have hij : i.val≠j.val := by
    intro he
    have he' : i=j := Fin.ext he
    subst j
    exact hne rfl
  exact Offset.sep work (by omega) (by omega_using []) (by omega_using [])

theorem saved_frame (m : Mem) (work : Addr) (v : VReg → BitVec 128) :
    Frame [⟨work+BitVec.ofNat 64 2048,128⟩] m (writeSlice (extraSlots 2048) work v m) := by
  refine writeSlice_frame _ _ _ _ _ ?_
  intro p hp
  obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
  exact Offset.contains work (e := 2048) (by omega_using []) (by omega_using []) (by decide)

theorem Saved.frame {m m' : Mem} {work : Addr} {v : VReg → BitVec 128}
    {rs : List Region} (h : Saved m work v) (hf : Frame rs m m')
    (hd : ∀r∈rs,(⟨work+BitVec.ofNat 64 2048,128⟩ : Region).Disjoint r) : Saved m' work v := by
  intro i
  have hc : (⟨work+BitVec.ofNat 64 2048,128⟩ : Region).Contains
      (work+BitVec.ofNat 64 (2048+16*i.val)) (128/8) :=
    Offset.contains work (e := 2048) (by omega_using []) (by omega_using []) (by decide)
  have he := hf.readW hc hd (by decide : 128/8<2^64)
  have hr : m'.read (work+BitVec.ofNat 64 (2048+16*i.val)) 16 =
      m.read (work+BitVec.ofNat 64 (2048+16*i.val)) 16 := by
    simpa only [Mem.readW,BitVec.setWidth_eq] using he
  exact hr.trans (h i)

/-- The inverse passes only write the first 2048 bytes of the work buffer. -/
theorem Saved.workFrame {m m' : Mem} {work : Addr} {v : VReg → BitVec 128}
    (h : Saved m work v) (hf : Frame [⟨work,2048⟩] m m') : Saved m' work v := by
  refine h.frame hf ?_
  intro r hr
  have he : r=⟨work,2048⟩ := List.mem_singleton.mp hr
  subst r
  exact Offset.disjoint_base work (d := 2048) (by decide) (by decide)

/-- At return x2 has advanced by 128 bytes, so restore offset1920 addresses the saved area. -/
theorem restore_saved {s : State} {work : Addr} {v : VReg → BitVec 128}
    (hx : s.gpr .x2=work+BitVec.ofNat 64 128) (hs : Saved s.mem work v)
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VG.Proof.MlKem.AArch64.VChg saved s t →
      (∀r∈saved,t.v r=v r) → WP isa (.block rest) t Q) :
    WP isa (.block (restoreCode++rest)) s Q := by
  refine restore_ok hr fun t ht hv => k t ht ?_
  intro r hr'
  have hex : ∃ i : Fin 8,r=savedReg i := by
    have he : saved=(List.finRange 8).map savedReg := rfl
    rw [he] at hr'
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hr'
    exact ⟨i,hi.symm⟩
  obtain ⟨i,rfl⟩ := hex
  have hh := hv (savedReg i,1920+16*i.val) ((extraSlots_mem _ _).mpr ⟨i,rfl⟩)
  rw [hx,BitVec.add_assoc,← BitVec.ofNat_add] at hh
  have he : 128+(1920+16*i.val)=2048+16*i.val := by omega_using []
  simpa only [he,hs i] using hh

theorem save_saved {s : State}
    (hr : ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VG.Proof.MlKem.AArch64.VMem s t
        (writeSlice (extraSlots 2048) (s.gpr .x0) s.v s.mem) →
      Saved t.mem (s.gpr .x0) s.v →
      Frame [⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩] s.mem t.mem →
      WP isa (.block rest) t Q) : WP isa (.block (save++rest)) s Q := by
  refine save_ok hr fun t ht => k t ht ?_ ?_
  · rw [ht.mem]; exact saved_after _ _ _
  · rw [ht.mem]; exact saved_frame _ _ _

theorem restore_preservedV {s₀ s : State} {work : Addr}
    (hx : s.gpr .x2=work+BitVec.ofNat 64 128) (hs : Saved s.mem work s₀.v)
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VG.Proof.MlKem.AArch64.VChg saved s t →
      (∀r∈preservedV,(t.v r).extractLsb' 0 64=(s₀.v r).extractLsb' 0 64) →
      WP isa (.block rest) t Q) : WP isa (.block (restoreCode++rest)) s Q := by
  refine restore_saved hx hs hr fun t ht hv => k t ht ?_
  intro r hr'
  rw [hv r hr']
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
