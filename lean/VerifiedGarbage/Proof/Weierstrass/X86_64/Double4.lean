import VerifiedGarbage.Proof.Mont.X86_64.Double4
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog

/-! Register-only doubling preserves the field-program invariant. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem double4_inv_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) {o a : Nat}
    (ho : Sl o) (ha : a∈V) :
    WP isa (.block (double4 M o a)) s fun t =>
      OpKeep M base o s t ∧ Inv M base size m Sl (o::V) (Function.update E o (E a+E a)) t := by
  have hao := hL.le a (hI.sl a ha)
  have hoo := hL.le o ho
  have hlt := hI.lt a ha
  rw [hn] at hao hoo hlt
  refine WP.mono (double4_ok hn hI.scr hI.mod hao hoo hlt) fun t ⟨hk,he⟩ => ?_
  refine ⟨hk,hI.update hL ho hk ?_ ?_⟩
  · rw [hn,he]
    exact Nat.mod_lt _ (by have := NeZero.ne m; omega)
  · rw [hn,he,Nat.two_mul,toM_add]
    have hv := hI.val a ha
    rw [hn] at hv
    rw [hv]

end VG.Proof.Weierstrass.X86_64
