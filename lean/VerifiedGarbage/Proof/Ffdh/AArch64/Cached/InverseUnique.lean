module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MontgomeryOne
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-! The imported inverse is public: an odd canonical modulus determines it uniquely. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem imported_inverse_unique {p : Parameters} {a b : BitVec 64} {s t : VG.AArch64.State}
 (left : FieldInitial {p with mi:=a} s) (right : FieldInitial {p with mi:=b} t) (odd : p.P%2=1) : a=b := by
 have invA : (p.P%2^64*a.toNat+1)%2^64=0 := by
  have h:=left.inverse
  change ((word s.mem p.B (slot p.w 0)).toNat*a.toNat+1)%2^64=0 at h
  rw [←wv_mod64 s.mem p.B (slot p.w 0) (n:=p.w) (by have :=p.positive;omega),left.modulus] at h
  exact h
 have invB : (p.P%2^64*b.toNat+1)%2^64=0 := by
  have h:=right.inverse
  change ((word t.mem p.B (slot p.w 0)).toNat*b.toNat+1)%2^64=0 at h
  rw [←wv_mod64 t.mem p.B (slot p.w 0) (n:=p.w) (by have :=p.positive;omega),right.modulus] at h
  exact h
 exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)];exact odd) invA invB

end VG.Proof.Ffdh.AArch64.Cached
