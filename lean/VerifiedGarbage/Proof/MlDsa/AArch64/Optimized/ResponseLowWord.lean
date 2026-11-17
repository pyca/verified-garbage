module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMath
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Response
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseWord
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `MlDsa.AArch64.Optimized.ResponseLowMath`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round

/-- The wrapped high-bit case is precisely the large positive remainder. -/
theorem lowBits_centered {g : Nat} (hg : IsG g) (r : Zq) :
    let a : Int := (r.val:Int)-(hbF g r.val%hbM g)*(2*g)
    lowBits g r=a-(if 4190208<a then 8380417 else 0) := by
  rw [lowBits_eq (mem_of_isG hg)]
  have hr := r.isLt
  rcases hg with rfl | rfl <;>
    simp only [hbF,hbM,q,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88] at * <;> omega_using []

theorem lowBits_bounds {g : Nat} (hg : IsG g) (r : Zq) :
    -(g:Int)≤lowBits g r ∧ lowBits g r≤(g:Int) := by
  rw [lowBits_eq (mem_of_isG hg)]
  have hr := r.isLt
  rcases hg with rfl | rfl <;>
    simp only [hbF,hbM,q,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88] at * <;> omega_using []

/-- The first conditional addition canonicalizes a reduced signed difference. -/
theorem reduce_signCorrected {x : BitVec 32} (hl : -2*8380417<x.toInt) (hh : x.toInt<3*8380417) :
    (Inverse.signCorrected (reduceWord x)).toNat=(ofInt x.toInt).val := by
  have h := reduce32_bounds hl hh
  have hi := reduceWord_int x hl hh
  have he := Inverse.signCorrected_int (reduceWord x) (by omega_using [h, hi]) (by omega_using [h, hi])
  have ht := BitVec.toInt_eq_toNat_cond (Inverse.signCorrected (reduceWord x))
  have hm := reduce32_mod x.toInt
  have hv := VG.Proof.MlDsa.KeyGen.ofInt_val x.toInt
  rw [hi] at he
  split at he <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

/-! ### `MlDsa.AArch64.Optimized.ResponseLowVec`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop vword_mapWords3)

theorem cadd_ok {d : VReg} (hd : d≠.v7) {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (k : ∀t,VChg [.v7,d] s t →
      (∀e<4,vword (t.v d) e=Inverse.signCorrected (vword (s.v d) e)) → WP isa (.block rest) t Q) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Response.cadd d++rest)) s Q := by
  refine wp_vop (d:=.v7) rfl fun a ha => wp_vop (d:=.v7) rfl fun b hb =>
    wp_vop (d:=d) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.get d hd,ha.get d hd,hb.v,Inverse.word_and,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v16 (by decide),hq e he]
    rfl

def lowCorrection : List Instr :=
  [.vop (.mls .v0 .v1 .v21),.vop (.sub .s4 .v6 .v26 .v0),
    .vop (.shift .sshr .s4 .v6 .v6 31),.vop (.logic .and .v6 .v6 .v16),
    .vop (.sub .s4 .v0 .v0 .v6)]

def lowWord (a h twoG : BitVec 32) : BitVec 32 :=
  let l := a-h*twoG
  l-((4190208#32-l).sshiftRight 31 &&& 8380417#32)

theorem lowCorrection_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v16) e=8380417#32)
    (hh : ∀e<4,vword (s.v .v26) e=4190208#32)
    (k : ∀t,VChg [.v0,.v6] s t → (∀e<4,vword (t.v .v0) e=
      lowWord (vword (s.v .v0) e) (vword (s.v .v1) e) (vword (s.v .v21) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (lowCorrection++rest)) s Q := by
  refine wp_vop (d:=.v0) rfl fun a ha => wp_vop (d:=.v6) rfl fun b hb =>
    wp_vop (d:=.v6) rfl fun c hc => wp_vop (d:=.v6) rfl fun d hd =>
    wp_vop (d:=.v0) rfl fun t ht => ?_
  have hk : VChg [.v0,.v6] s t :=
    ((((ha.chg.trans hb.chg).trans hc.chg).trans hd.chg).trans ht.chg).mono (by decide)
  refine k t hk ?_
  intro e he
  rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hd.get .v0 (by decide),hc.get .v0 (by decide),
    hb.get .v0 (by decide),hd.v,Inverse.word_and,hc.v,VG.AArch64.vword_map2 _ _ _ he,
    hb.v,VG.AArch64.vword_map2 _ _ _ he,ha.get .v26 (by decide),hh e he,
    hc.get .v16 (by decide),hb.get .v16 (by decide),ha.get .v16 (by decide),hq e he,
    ha.v,vword_mapWords3 _ _ _ _ he]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Round

theorem centeredCorrection_int {l : BitVec 32} (hl : -8380417<l.toInt) (hh : l.toInt<8380417) :
    (l-((4190208#32-l).sshiftRight 31 &&& 8380417#32)).toInt=
      l.toInt-(if 4190208<l.toInt then 8380417 else 0) := by
  have ht := BitVec.toInt_eq_toNat_cond (4190208#32-l)
  have hd : (4190208#32-l).toInt=4190208-l.toInt :=
    subWord_int _ _ (by change -2147483648≤4190208-l.toInt; omega_using [hh])
      (by change 4190208-l.toInt<2147483648; omega_using [hl])
  rw [ResidentMask.signMask32]
  by_cases h : 4190208<l.toInt
  · rw [ite_eq_right (by omega),ite_eq_left h]
    rw [show (-1:BitVec 32) &&& 8380417#32=8380417#32 by decide]
    exact subWord_int _ _ (by change -2147483648≤l.toInt-8380417; omega_using [hl])
      (by change l.toInt-8380417<2147483648; omega_using [hh])
  · rw [ite_eq_left (by omega),ite_eq_right h]
    simp

theorem lowWord_spec {g : Nat} (hg : IsG g) {a : BitVec 32} (ha : a.toNat<q) :
    (lowWord a (HighPack.highWord g a) (BitVec.ofNat 32 (2*g))).toInt=
      lowBits g ⟨a.toNat,ha⟩ := by
  have hhigh := HighPack.highWord_toNat hg ha
  have hraw : (a-HighPack.highWord g a*BitVec.ofNat 32 (2*g)).toInt=
      (a.toNat:Int)-(VG.Proof.MlDsa.Round.hbF g a.toNat%hbM g)*(2*g) := by
    have ht := BitVec.toInt_eq_toNat_cond (a-HighPack.highWord g a*BitVec.ofNat 32 (2*g))
    simp only [BitVec.toNat_sub,BitVec.toNat_mul,BitVec.toNat_ofNat] at ht
    rw [hhigh] at ht
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,q] at * <;> omega_using [ha, ht]
  have hb : -8380417<(a-HighPack.highWord g a*BitVec.ofNat 32 (2*g)).toInt ∧
      (a-HighPack.highWord g a*BitVec.ofNat 32 (2*g)).toInt<8380417 := by
    rw [hraw]
    have hr : a.toNat<8380417 := ha
    rcases hg with rfl | rfl <;>
      simp only [hbM,Impl.MlDsa.AArch64.Round.g32,Impl.MlDsa.AArch64.Round.g88,q] at * <;> omega_using [ha]
  rw [lowWord,centeredCorrection_int hb.1 hb.2,hraw,lowBits_centered hg]

theorem subInput_word {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    (Inverse.signCorrected (reduceWord (a-b))).toNat=(ofInt ((a.toNat:Int)-b.toInt)).val := by
  have hat := BitVec.toInt_eq_toNat_cond a
  have ha' : a.toNat<8380417 := ha
  have hai : a.toInt=(a.toNat:Int) := by omega_using [hat, ha']
  have hab := subWord_int a b (by rw [hai]; omega_using [bh]) (by rw [hai]; omega_using [bl, ha'])
  rw [hai] at hab
  rw [reduce_signCorrected (by rw [hab]; omega_using [bh]) (by rw [hab]; omega_using [bl, ha']),hab]

theorem subLow_word {g : Nat} (hg : IsG g) {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    let c := Inverse.signCorrected (reduceWord (a-b))
    (lowWord c (HighPack.highWord g c) (BitVec.ofNat 32 (2*g))).toInt=
      lowBits g (ofInt ((a.toNat:Int)-b.toInt)) := by
  dsimp only
  have hc := subInput_word ha bl bh
  have cb : (Inverse.signCorrected (reduceWord (a-b))).toNat<q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowWord_spec hg cb]
  congr 1
  exact Fin.ext hc

theorem subHigh_word {g : Nat} (hg : IsG g) {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    (HighPack.highWord g (Inverse.signCorrected (reduceWord (a-b)))).toNat=
      (highBits g (ofInt ((a.toNat:Int)-b.toInt))).toNat := by
  have hc := subInput_word ha bl bh
  have cb : (Inverse.signCorrected (reduceWord (a-b))).toNat<q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [HighPack.highWord_spec hg cb]
  congr 2
  exact Fin.ext hc

theorem subLow_norm {g B : Nat} (hg : IsG g) {a b : BitVec 32} (ha : a.toNat<q)
    (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    let c := Inverse.signCorrected (reduceWord (a-b))
    normMask (lowWord c (HighPack.highWord g c) (BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (ofInt ((a.toNat:Int)-b.toInt))))<B then 0 else -1 := by
  dsimp only
  have hi := subLow_word hg ha bl bh
  have hbnd := lowBits_bounds hg (ofInt ((a.toNat:Int)-b.toInt))
  have hg' : g≤261888 := by rcases hg with rfl | rfl <;> decide
  rw [normMask_value (hB:=hB) (hB':=hB') (by rw [hi]; omega_using [hbnd, hg']) (by rw [hi]; omega_using [hbnd, hg']),hi]
  have hn := reduced_norm_iff (lowBits g (ofInt ((a.toNat:Int)-b.toInt))) B (by omega_using [hbnd, hg']) (by omega_using [hbnd, hg']) hB'
  by_cases h : normZq (ofInt (lowBits g (ofInt ((a.toNat:Int)-b.toInt))))<B
  · rw [ite_eq_left h,ite_eq_left (hn.mp h)]
  · rw [ite_eq_right h,ite_eq_right (fun he => h (hn.mpr he))]

end VG.Proof.MlDsa.AArch64.Optimized.Response
