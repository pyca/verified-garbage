import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.Exp

/-! The last public-exponent multiplication also leaves Montgomery form. -/
namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

/-- Keep the reduced accumulator on the right: the input need not be reduced,
including when an invalid signature will subsequently be masked out. -/
theorem final_factor_ok (M : Mont) {s : State} {B : Addr} {Z w N x u e : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hN : wv s.mem B (slot w aN) w = N)
    (hi : ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2^64 = 0)
    (hR : Nat.Coprime (2^(64*w)) N)
    (hX : wv s.mem B (slot w aX) w = u)
    (hY : wv s.mem B (slot w aY) w < N)
    (hc : wv s.mem B (slot w aY) w % N = x^e * 2^(64*w) % N) :
    WP isa (M.mm aY aX aY) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w aY) w = x^e * u % N ∧
      Arrays B w [aAcc,aTmp,aY] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (M.mm_ok hg hZ hw hw' (o := aY) (a := aX) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hi (by rw [hN]; exact hY)) fun t ⟨ht,lt,eq,frame,keep⟩ => ?_
  rw [hN] at lt eq
  rw [hX, Nat.mul_comm u] at eq
  have result := VG.Proof.Bignum.mont_final_factor hR hc eq
  rw [Nat.mod_eq_of_lt lt] at result
  exact ⟨ht,result,frame,keep⟩

end VG.Proof.Bignum.X86_64.FoldedPublic
