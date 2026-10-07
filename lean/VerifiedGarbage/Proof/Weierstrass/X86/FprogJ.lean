import VerifiedGarbage.Proof.Weierstrass.X86.Rcb3
import VerifiedGarbage.Proof.Weierstrass.JacMadd

/-!
# The mixed Jacobian addition's code on x86 (32-bit)

`maddJ_ok`: the code of `maddJ` computes `maddJF` on the slots' values,
using the generic numbered-formula proof shared with complete additions.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- `o = p + q` by the mixed Jacobian addition (`q` affine: `q.z` is not
read). -/
theorem maddJ_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog M wk (maddJ S p q o)) s fun s' => ProgKeep M base wk (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (maddJ S p q o) E) s' ∧
      (runOps (maddJ S p q o) E o.x, runOps (maddJ S p q o) E o.y, runOps (maddJ S p q o) E o.z) =
        maddJF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) := by
  rw [maddJ_eq]
  exact WP.mono (ofN_ok hL hW hm maddJN_ok hA hSl hI hV) fun s' ⟨k, I, v⟩ =>
    ⟨k, I, v.trans (maddJN_run _)⟩

end VG.Proof.Weierstrass.X86
