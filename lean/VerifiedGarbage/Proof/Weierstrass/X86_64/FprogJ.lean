import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Weierstrass.JacMadd

/-!
# The mixed Jacobian addition's code on x86-64

`maddJ_ok`: the code of `maddJ` computes `maddJF` on the slots' values, as
`rcb3m_ok` does Algorithm 5's.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass

/-- `o = p + q` by the mixed Jacobian addition (`q` affine: `q.z` is not
read). -/
theorem maddJ_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (maddJ S p q o)).inline s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (maddJ S p q o) E) s' ∧
      (runOps (maddJ S p q o) E o.x, runOps (maddJ S p q o) E o.y, runOps (maddJ S p q o) E o.z) =
        maddJF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) := by
  rw [maddJ_eq]
  exact WP.mono (ofN_ok hL hm maddJN_ok hA hSl hI hV) fun s' ⟨k, I, v⟩ =>
    ⟨k, I, v.trans (maddJN_run _)⟩

end VG.Proof.Weierstrass.X86_64
