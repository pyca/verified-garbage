module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedReduce
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

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
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega
  have hb : -8380417<(a-highWord g a*BitVec.ofNat 32 (2*g)).toInt ∧
      (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt<8380417 := by
    rw [hraw]
    have hr : a.toNat<8380417 := ha
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,Spec.MlDsa.q] at * <;> omega
  have hreduce := Response.reduceWord_int (a-highWord g a*BitVec.ofNat 32 (2*g)) (by omega) (by omega)
  rw [hreduce]
  have hrange := reduce32_bounds (x := (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt) (by omega) (by omega)
  have hmod := reduce32_mod (a-highWord g a*BitVec.ofNat 32 (2*g)).toInt
  have hlow := Response.lowBits_centered hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hlrange := Response.lowBits_bounds hg (⟨a.toNat,ha⟩ : Spec.MlDsa.Zq)
  have hgsmall : g≤261888 := by rcases hg with rfl | rfl <;> decide
  change Spec.MlDsa.lowBits g ⟨a.toNat,ha⟩ = _ at hlow
  rw [← hraw] at hlow
  split at hlow <;> omega

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
  refine wp_ldrq (by omega) rfl hread fun s1 h1 => ?_
  refine wp_ldrq (by omega) rfl (by rw [h1.rd,h1.wr,h1.gpr]; exact hread') fun s2 h2 => ?_
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
