module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointOps
import VerifiedGarbage.Proof.Framework.Omega


/-! Arithmetic block results lift to the ordinary-field point environment. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

def PointOp.natural (op : PointOp) (v : Nat → Nat) (p : Nat) : Nat :=
  match op with
  | .mul _ a b _ => v a*v b
  | .add _ a b => v a+v b
  | .sub _ a b => v a+p-v b
  | .cms _ C a D b => C*v a+D*(p-v b)

structure PointResult (base : Addr) (p : Nat) (loc : Nat → Nat) (op : PointOp) (s t : State) : Prop where
  bound : wordsVal t.mem base (loc op.out) 9<op.cap*p
  value : wordsVal t.mem base (loc op.out) 9%p=op.natural (fun x => wordsVal s.mem base (loc x) 9) p%p
  outside : Outside base (loc op.out) 72 s.mem t.mem

theorem OrdinaryInv.point_update {base : Addr} {p : Nat} [NeZero p] {loc : Nat → Nat}
    {V : List Nat} {E : Nat → Fin p} {caps : Nat → Nat} {s t : State} (h : OrdinaryInv base p loc V E caps s)
    (op : PointOp) (reads : ∀x∈op.ins,x∈V)
    (ranges : ∀x∈op.ins,caps x≤1 ∨ ∃C a D b,op=PointOp.cms op.out C a D b ∧ x=a ∧ caps x≤2)
    (result : PointResult base p loc op s t)
    (apart : ∀x∈V,x≠op.out → loc x+72≤loc op.out ∨ loc op.out+72≤loc x)
    (fits : ∀x∈V,loc x+72≤2^64)
    (cmsRight : ∀o C a D b,op=PointOp.cms o C a D b → caps b≤1) :
    OrdinaryInv base p loc (op.out::V) (op.run E) (Function.update caps op.out op.cap) t := by
  have outValue : Fin.ofNat p (wordsVal t.mem base (loc op.out) 9)=
      Fin.ofNat p (op.natural (fun x => wordsVal s.mem base (loc x) 9) p) := ofNat_eq_ofNat.mpr result.value
  have values (x : Nat) (hx : x∈op.ins) := h.value x (reads x hx)
  have rhsBound (b : Nat) (hb : b∈V) (hc : caps b≤1) : wordsVal s.mem base (loc b) 9<p := by
    have e := Nat.mul_le_mul_right p hc
    simp only [Nat.one_mul] at e
    exact Nat.lt_of_lt_of_le (h.bound b hb) e
  cases op with
  | mul o a b weak =>
    simp only [PointOp.natural] at outValue
    rw [ofNat_mul',values a (by simp [PointOp.ins]),values b (by simp [PointOp.ins])] at outValue
    exact h.update result.outside apart fits result.bound outValue
  | add o a b =>
    simp only [PointOp.natural] at outValue
    rw [ofNat_add',values a (by simp [PointOp.ins]),values b (by simp [PointOp.ins])] at outValue
    exact h.update result.outside apart fits result.bound outValue
  | sub o a b =>
    have capb : caps b≤1 := by
      rcases ranges b (by simp [PointOp.ins]) with hc|⟨C,a,D,b,he,_,_⟩
      · exact hc
      · cases he
    have hb := rhsBound b (reads b (by simp [PointOp.ins])) capb
    have he := ordinary_sub (a:=wordsVal s.mem base (loc a) 9) (by omega_arith : wordsVal s.mem base (loc b) 9≤wordsVal s.mem base (loc a) 9+p)
    rw [ofNat_mod] at he
    simp only [PointOp.natural] at outValue
    rw [he,values a (by simp [PointOp.ins]),values b (by simp [PointOp.ins])] at outValue
    exact h.update result.outside apart fits result.bound outValue
  | cms o C a D b =>
    have hb := rhsBound b (reads b (by simp [PointOp.ins])) (cmsRight o C a D b rfl)
    have he := ordinary_cms C (wordsVal s.mem base (loc a) 9) D (wordsVal s.mem base (loc b) 9) (Nat.le_of_lt hb)
    rw [ofNat_mod] at he
    simp only [PointOp.natural] at outValue
    rw [he,values a (by simp [PointOp.ins]),values b (by simp [PointOp.ins])] at outValue
    exact h.update result.outside apart fits result.bound outValue

end VG.Proof.Mont.AArch64.P521Field
