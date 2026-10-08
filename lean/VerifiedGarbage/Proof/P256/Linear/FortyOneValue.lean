import VerifiedGarbage.Proof.P256.Linear.FortyOneWords

namespace VG.Proof.P256.Linear.FortyOne
open VG.Proof.Ed25519.Word64
open Weak (W4 value addWords subWords addWords_value subWords_value value_lt)

def result (a b : W4) : W4 :=
  let u:=shift2 a
  let v:=subWords u.1 b
  let q:=quotient u.2 v.2
  let w:=addWords v.1 (correction q)
  addBack w.1 w.2

theorem canonical_nat {a b out : Nat} (hb : b<p)
    (hf : (out:Int)=(4*(a:Int)-(b:Int))%(p:Int)) : out=(4*a+p-b)%p := by
  have he : ((4*a+p-b:Nat):Int)=(4*(a:Int)-(b:Int))+(p:Int) := by omega
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod,he,Int.add_emod_right]
  exact hf

theorem result_value (a b : W4) (ha : value a<p) (hb : value b<p) :
    value (result a b)=(4*value a+p-value b)%p := by
  let u:=shift2 a
  let v:=subWords u.1 b
  let q:=quotient u.2 v.2
  let w:=addWords v.1 (correction q)
  let n : Int := 4*(value a:Int)-(value b:Int)
  have hu := shift2_value a
  have hv := subWords_value u.1 b
  have huv : u.2.toNat<4 := by
    change (a.2.2.2 >>> 62).toNat<4
    have := a.2.2.2.isLt
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    omega
  have hq := quotient_value u.2 v.2 huv
  have hc := Bool.toNat_le v.2
  have hq4 : q.toNat≤4 := by dsimp only [q]; omega
  have hn0 : -(p:Int)≤n := by dsimp only [n]; omega
  have hn1 : n<21*(p:Int) := by dsimp only [n]; omega
  have hvl := value_lt v.1
  have he : n=(value v.1:Int)+(radix:Int)*((q.toNat:Int)-1) := by
    change value u.1+radix*u.2.toNat=4*value a at hu
    change value v.1+value b=value u.1+Weak.R*(1-v.2.toNat) at hv
    change q.toNat=u.2.toNat+v.2.toNat at hq
    dsimp only [n]
    simp only [radix,Weak.R] at hu hv ⊢
    omega
  have hquot : (q.toNat:Int)=n/(radix:Int)+1 := by
    simp only [radix,Weak.R] at he hvl ⊢
    omega
  have hw := addWords_value v.1 (correction q)
  rw [correction_value q hq4] at hw
  have hw' : (value w.1:Int)+(radix:Int)*(w.2.toNat:Int)-radix=
      n-(n/(radix:Int)+1)*(p:Int) := by
    change value w.1+Weak.R*w.2.toNat=value v.1+q.toNat*(radix-p) at hw
    rw [←hquot]
    simp only [radix,Weak.R,p,VG.Spec.P256.p] at hw he ⊢
    omega
  have hf := addBack_value w.1 w.2 hn0 hn1 hw'
  change (value (result a b):Int)=n%(p:Int) at hf
  exact canonical_nat hb hf
end VG.Proof.P256.Linear.FortyOne
