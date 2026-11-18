module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
public import VerifiedGarbage.Proof.MlKem.Ntt
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlKem.AArch64.Ntt16.Readonly.Words`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16
open VG.Impl.MlKem.AArch64.Ntt16.Readonly

theorem forward_length : (words 16 tableHalves).length = 64 := by lit_decide
theorem gamma_length : (words 32 gammaTable).length = 64 := by lit_decide

theorem forward_words : ∀ i < 64, (words 16 tableHalves).getD i 0 = hw4 tableHalves i := by lit_decide

theorem gamma_low : ∀ i < 64,
    ((words 32 gammaTable).getD i 0).extractLsb' 0 32 = BitVec.ofNat 32 (gammaTable.getD (2*i) 0) := by lit_decide

theorem gamma_high : ∀ i < 64,
    ((words 32 gammaTable).getD i 0).extractLsb' 32 32 = BitVec.ofNat 32 (gammaTable.getD (2*i+1) 0) := by lit_decide

end VG.Proof.MlKem.AArch64.Ntt16.Readonly

end

end

/-! ### `MlKem.AArch64.Dot.Result`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Dot.Field`, which this module and modules that import it used -/

section

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
  omega_using []

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
  · rw [next_even,h.1,add_get _ _ (by change 2*i < 256; omega_using [hi]),val_add',multiply_even_val _ _ hi]
  · rw [next_cross,h.2,add_get _ _ (by change 2*i+1 < 256; omega_using [hi]),val_add',multiply_odd_val _ _ hi]

theorem sumTerms_field (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly)
    {c e : Nat} (hc : c < 32) (he : e < 4) {a : Nat → Sums} {P : Poly}
    (h : PairRel (a e) P (4*c+e)) :
    PairRel (sumTerms terms (blockValues (polyValues F) c) (blockValues (polyValues G) c) a e)
      (polySum terms F G P) (4*c+e) := by
  induction terms generalizing a P with
  | nil => exact h
  | cons fg terms ih =>
    apply ih
    have hn := h.next (F := F fg) (G := G fg) (by omega_using [hc, he])
    simpa only [advance,blockValues,polyValues,show 8*c+2*e = 2*(4*c+e) by omega_using [],
      show 8*c+(2*e+1) = 2*(4*c+e)+1 by omega_using []] using hn

end VG.Proof.MlKem.AArch64.Dot

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.Spec.MlKem VG.Proof.MlKem

def gammaValues (i : Nat) : Nat := (gamma i).val

theorem zero_pair {i : Nat} (hi : i < 128) : PairRel (zeroSums 0) zero i := by
  constructor
  · rw [zero_get (by change 2*i<256; omega_using [hi])]
    simp only [zeroSums,Nat.zero_mul,Nat.add_zero,Nat.zero_mod,val_zero]
  · rw [zero_get (by change 2*i+1<256; omega_using [hi])]; rfl

theorem result_field (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Poly)
    {j : Nat} (hj : j < 256) :
    result terms (polyValues F) (polyValues G) gammaValues j =
      BitVec.ofNat 32 ((polySum terms F G)[j]!).val := by
  have hc : j/8 < 32 := by omega_using [hj]
  have he : j%8/2 < 4 := by omega_using []
  have hh := sumTerms_field terms F G hc he (a := zeroSums) (P := zero)
    (zero_pair (i := 4*(j/8)+j%8/2) (by omega_using [hj]))
  unfold result interleave
  split <;> rename_i hp
  · have ji : j = 2*(4*(j/8)+j%8/2) := by omega_using [hp]
    change BitVec.ofNat 32 (((sumTerms terms (blockValues (polyValues F) (j/8))
      (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).even +
      (sumTerms terms (blockValues (polyValues F) (j/8)) (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).odd *
      (gamma (4*(j/8)+j%8/2)).val)%q) = _
    rw [hh.1,←ji]
  · have ji : j = 2*(4*(j/8)+j%8/2)+1 := by omega_using [hp]
    change BitVec.ofNat 32 ((sumTerms terms (blockValues (polyValues F) (j/8))
      (blockValues (polyValues G) (j/8)) zeroSums (j%8/2)).cross%q) = _
    rw [hh.2,←ji]

end VG.Proof.MlKem.AArch64.Dot

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16.Readonly

/-- The emitted readonly gamma artifact, as its 64 doublewords. -/
def GammaArtifact (m : Mem) (p : Addr) : Prop :=
  ∀ i < 64, m.readW (p+BitVec.ofNat 64 (8*i)) 64 = (words 32 gammaTable).getD i 0

theorem GammaArtifact.word {m : Mem} {p : Addr} (h : GammaArtifact m p)
    {k : Nat} (hk : k < 128) :
    m.readW (p+BitVec.ofNat 64 (4*k)) 32 = BitVec.ofNat 32 (gammaValues k) := by
  have hi : k/2 < 64 := by omega_using [hk]
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega_using []
  have hg : gammaTable.getD k 0 = gammaValues k := by
    rw [gammaTable_eq,gammas_getD hk]; rfl
  rw [←hg]
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,Ntt16.Readonly.gamma_low _ hi] at hx
    simpa only [show 8*(k/2)=4*k by omega_using [hr],←he] using hx
  · have he : k=2*(k/2)+1 := by omega_using [hr]
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,Ntt16.Readonly.gamma_high _ hi,BitVec.add_assoc,
      ←BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega_using [hr],←he] using hx

theorem GammaArtifact.lanes {m : Mem} {p : Addr} (h : GammaArtifact m p)
    {c : Nat} (hc : c < 32) :
    Lanes (m.read (p+BitVec.ofNat 64 (16*c)) 16) (blockGamma gammaValues c) := by
  have hs : p+BitVec.ofNat 64 (16*c) = coeffAddr p (4*c) := by
    unfold coeffAddr; congr 2; omega_using []
  rw [hs]
  apply lanes_coeffs (m:=m) (p:=p) (j:=4*c)
  intro e he
  change (m.readW (p+BitVec.ofNat 64 (4*(4*c+e))) 32).toNat = gammaValues (4*c+e)
  rw [h.word (by omega_using [hc, he]),BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  exact Nat.lt_trans (gamma (4*c+e)).isLt (by decide)

end VG.Proof.MlKem.AArch64.Dot
