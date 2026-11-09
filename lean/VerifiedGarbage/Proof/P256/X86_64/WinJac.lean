module
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublic
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# P-256 on x86-64: the Jacobian window method with the doubling by halving

The doubling by halving (`doubleHalfPublic`, `doubleHalfPublic_ok`) is a
doubling the Jacobian window method can use (`doubleHalfPublic_dblOk`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.P256.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

/-- The doubling by halving doubles a Jacobian triple in place. -/
theorem doubleHalfPublic_dblOk {M : Mod} {S : RcbSlots} (hn : M.n = 4)
    (hm : UnitMod Spec.P256.p (2 ^ (64 * M.n))) (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve) :
    DblOk M S Spec.P256.curve (doubleHalfPublic M S) := by
  intro base size Sl hL p hnd hSl E s hI Q hQ hJ
  have hsub : (doubleSlots S p).Sublist (rcbW S p) :=
    .cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.refl _))))))
  refine WP.mono (doubleHalfPublic_ok hn hL hm hC ha (hnd.sublist hsub) (fun x hx => hSl x (hsub.subset hx))
    hI (fun x hx => hx) hQ hJ) fun t ⟨k, I, J⟩ =>
    ⟨k.mono fun x hx => hsub.subset hx, _, I.sub fun x hx => List.mem_append_left _ hx, J⟩

end VG.Proof.P256.X86_64
