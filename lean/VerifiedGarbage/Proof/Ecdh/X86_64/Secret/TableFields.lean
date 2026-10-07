import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableLoad
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableStore
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTransfer

/-! Field invariants for the table-builder's copies, including both cached Z powers. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Mont
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 Spec.Weierstrass

def tableSource (K : WinCfg) (i : Nat) : Nat :=
  if i<3 then K.R.x+32*i else K.E.x+96+32*(i-3)

theorem tableStore_fields_ok {K : WinCfg} {base : Addr} {size j : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p Sl V E s)
    (hj1 : 1≤j) (hj16 : j≤16) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (ht : K.tbl<2^31) (hT : K.tbl+2560≤size) (hR : K.R.x+96≤size) (hE : K.E.x+160≤size)
    (hRT : K.R.x+96≤K.tbl ∨ K.tbl+2560≤K.R.x)
    (hET : K.E.x+160≤K.tbl ∨ K.tbl+2560≤K.E.x+96)
    (hD : ∀ x∈consecutiveFields (K.tbl+160*(j-1)) 5,Sl x)
    (hQ : ∀ i<5,tableSource K i∈V) :
    WP isa (.block (Impl.Ecdh.X86_64.Window5.tableStore K)) s fun t =>
      ProgKeep K.M base (consecutiveFields (K.tbl+160*(j-1)) 5) s t ∧
      Inv K.M base size C.p Sl (consecutiveFields (K.tbl+160*(j-1)) 5++V) (tmv C K.M.n base t) t ∧
      ∀ i<5,tmv C K.M.n base t (K.tbl+160*(j-1)+32*i)=E (tableSource K i) := by
  refine WP.mono (tableStore_ok hI.scr hj1 hj16 hc ht hT hR hE hRT hET)
    fun t ⟨vp,vc,hk,ho⟩ => hI.transferConsecutiveFields hL hn hD hQ ?_ hk ho
  intro i hi
  rw [hn]
  by_cases hp : i<3
  · simpa only [tableSource,hp,ite_true] using vp i hp
  · have he : K.tbl+160*(j-1)+32*i=K.tbl+160*(j-1)+96+32*(i-3) := by omega
    rw [he]
    simpa only [tableSource,hp,ite_false] using vc (i-3) (by omega)

theorem tableLoad_fields_ok {K : WinCfg} {base : Addr} {size j : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hn : K.M.n=4)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p Sl V E s)
    (h2 : 2≤j) (h16 : j≤16) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (ht : K.tbl<2^31) (hT : K.tbl+2560≤size) (hR : K.R.x+96≤size)
    (hRT : K.R.x+96≤K.tbl ∨ K.tbl+2560≤K.R.x)
    (hD : ∀ x∈consecutiveFields K.R.x 3,Sl x)
    (hQ : ∀ i<3,K.tbl+160*(tableParent j-1)+32*i∈V) :
    WP isa (Impl.Ecdh.X86_64.Window5.tableLoad K) s fun t =>
      ProgKeep K.M base (consecutiveFields K.R.x 3) s t ∧
      Inv K.M base size C.p Sl (consecutiveFields K.R.x 3++V) (tmv C K.M.n base t) t ∧
      ∀ i<3,tmv C K.M.n base t (K.R.x+32*i)=E (K.tbl+160*(tableParent j-1)+32*i) := by
  refine WP.mono (tableLoad_ok hI.scr h2 h16 hc ht hT hR hRT)
    fun t ⟨hv,hk,ho⟩ => hI.transferConsecutiveFields hL hn hD hQ ?_ hk ho
  intro i hi
  rw [hn]
  exact hv i hi

end VG.Proof.Ecdh.X86_64.Secret
