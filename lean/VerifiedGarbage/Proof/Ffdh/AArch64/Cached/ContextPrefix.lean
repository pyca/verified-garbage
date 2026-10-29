module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Context
import VerifiedGarbage.Proof.Mont.WordsCanonical
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! The canonical context contains exact, unreduced-width p and reduced R² limbs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem context_prefix {m : Mem} {ctx : Addr} {count k : Nat} {dom : List Byte}
 (length : k≤dom.length) (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (dom.take k)) k=true)
 (canonical : Spec.Ffdh.generationContextAt m ctx count k dom) :
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 wv m ctx 24 w=P ∧ wv m ctx (24+8*w) w=2^(128*w)%P := by
 dsimp only
 let w := Spec.Rsa.modulusWords k
 let P := (Spec.Ffdh.domainOf k dom).p
 have countEq : count=3+34*w := context_words_count canonical
 have bound : P<2^(64*w) := by
  have h := os2ip_lt (dom.take k)
  have len : (dom.take k).length=k := by simp only [List.length_take];omega
  rw [len,pow256_eq] at h
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by dsimp [w,Spec.Rsa.modulusWords];omega))
 have positive : 0<P := by
  have h := valid
  simp only [Spec.Rsa.modulusValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  change 0<Spec.Rsa.os2ip (dom.take k)
  omega
 have prefixWords : Spec.Rsa.wordsAt m (off ctx 24) (2*w)=Spec.Rsa.toWords P w++Spec.Rsa.toWords (2^(128*w)%P) w := by
  have slice := VG.Proof.Mont.wordsAt_slice m ctx 0 count 3 (2*w) (by omega)
  have src := context_words length valid canonical
  simp only [VG.Proof.Mont.off,BitVec.add_zero,Nat.zero_add] at slice
  rw [src] at slice
  rw [VG.Proof.Ffdh.generationValues_montgomery] at slice
  exact slice.symm
 have values := pre_words prefixWords bound (Nat.lt_trans (Nat.mod_lt _ positive) bound)
 have zero : wv m (off ctx 24) 0 w=wv m ctx 24 w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.zero_add]
 have second : wv m (off ctx 24) (8*w) w=wv m ctx (24+8*w) w := by
  apply wv_congr2
  intro i hi
  simp only [word,off,BitVec.ofNat_add,BitVec.add_assoc,Nat.add_assoc]
 exact ⟨zero.symm.trans values.1,second.symm.trans values.2⟩

end VG.Proof.Ffdh.AArch64.Cached
