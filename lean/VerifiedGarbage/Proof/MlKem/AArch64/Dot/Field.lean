module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
public import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.MlKem.Arith

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.Spec.MlKem VG.Proof.MlKem

def polySum (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly) (P : Poly := zero) : Poly :=
  terms.foldl (fun p fg => add p (multiplyNTTs (F fg) (G fg))) P

def polyValues (F : (Nat × Nat) → Poly) : (Nat × Nat) → Nat → Nat := fun fg i => ((F fg)[i]!).val

def PairRel (a : Sums) (P : Poly) (i : Nat) : Prop :=
  (a.even + a.odd * (gamma i).val) % q = (P[2*i]!).val ∧
  a.cross % q = (P[2*i+1]!).val

theorem next_even (s : Sums) (fe fo ge go g : Nat) :
    ((s.next fe fo ge go).even + (s.next fe fo ge go).odd*g)%q =
      ((s.even+s.odd*g)%q + (fe*ge+fo*go*g)%q)%q := by
  rw [←Nat.add_mod]
  change (s.even+fe*ge+(s.odd+fo*go)*g)%q = _
  rw [Nat.add_mul]
  congr 1
  omega

theorem next_cross (s : Sums) (fe fo ge go : Nat) :
    (s.next fe fo ge go).cross%q = (s.cross%q + (fe*go+fo*ge)%q)%q := by
  rw [←Nat.add_mod]
  change (s.cross+fe*go+fo*ge)%q = _
  rw [Nat.add_assoc]

theorem multiply_even_val (F G : Poly) {i : Nat} (hi : i < 128) :
    ((multiplyNTTs F G)[2*i]!).val =
      ((F[2*i]!).val*(G[2*i]!).val + (F[2*i+1]!).val*(G[2*i+1]!).val*(gamma i).val)%q := by
  rw [multiplyNTTs_even F G hi,val_add',val_mul,val_mul,val_mul,Nat.mod_mul_mod,←Nat.add_mod]

theorem multiply_odd_val (F G : Poly) {i : Nat} (hi : i < 128) :
    ((multiplyNTTs F G)[2*i+1]!).val =
      ((F[2*i]!).val*(G[2*i+1]!).val + (F[2*i+1]!).val*(G[2*i]!).val)%q := by
  rw [multiplyNTTs_odd F G hi,val_add',val_mul,val_mul,←Nat.add_mod]

theorem PairRel.next {a : Sums} {P F G : Poly} {i : Nat} (hi : i < 128) (h : PairRel a P i) :
    PairRel (a.next (F[2*i]!).val (F[2*i+1]!).val (G[2*i]!).val (G[2*i+1]!).val)
      (add P (multiplyNTTs F G)) i := by
  constructor
  · rw [next_even,h.1,add_get _ _ (by change 2*i < 256; omega),val_add',multiply_even_val _ _ hi]
  · rw [next_cross,h.2,add_get _ _ (by change 2*i+1 < 256; omega),val_add',multiply_odd_val _ _ hi]

theorem sumTerms_field (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly)
    {c e : Nat} (hc : c < 32) (he : e < 4) {a : Nat → Sums} {P : Poly}
    (h : PairRel (a e) P (4*c+e)) :
    PairRel (sumTerms terms (blockValues (polyValues F) c) (blockValues (polyValues G) c) a e)
      (polySum terms F G P) (4*c+e) := by
  induction terms generalizing a P with
  | nil => exact h
  | cons fg terms ih =>
    apply ih
    have hn := h.next (F := F fg) (G := G fg) (by omega)
    simpa only [advance,blockValues,polyValues,show 8*c+2*e = 2*(4*c+e) by omega,
      show 8*c+(2*e+1) = 2*(4*c+e)+1 by omega] using hn

end VG.Proof.MlKem.AArch64.Dot
