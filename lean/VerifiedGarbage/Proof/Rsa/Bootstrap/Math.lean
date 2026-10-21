module

public import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.Math

/-! # Squaring the Montgomery representation of a power of two -/

@[expose] public section
namespace VG.Proof.Rsa.Bootstrap

theorem square_encoded {e R M a c : Nat}
    (coprime : Nat.Coprime R M) (canonical : c < M)
    (encoded : a = 2^e*R%M) (square : c*R%M=a*a%M) :
    c = 2^(2*e)*R%M := by
  have h := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded (g:=2) (E:=e)
    coprime canonical (by simpa [VG.Proof.Bignum.powMod_eq,Nat.mod_mul_mod] using encoded) square
  simpa [VG.Proof.Bignum.powMod_eq,Nat.mod_mul_mod] using h

theorem seed_encoded (bits t : Nat) : 2^(bits+t) = 2^t*2^bits := by
  rw [Nat.pow_add,Nat.mul_comm]

theorem final_encoded {bits t j M : Nat} (h : t*2^j=bits) :
    2^(t*2^j)*2^bits%M = 2^(2*bits)%M := by
  rw [h,← Nat.pow_add]
  congr 2
  omega

end VG.Proof.Rsa.Bootstrap
