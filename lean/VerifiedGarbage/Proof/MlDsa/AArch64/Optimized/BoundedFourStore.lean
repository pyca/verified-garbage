import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.Sample.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16)

/-- A full vector store is safe with four free slots; only its accepted prefix
extends the meaningful scalar output. Later lanes may be overwritten. -/
theorem stored_append_vector {m : Mem} {p : Addr} {L A : List Zq} {v : BitVec 128}
    (hL : L.length+4≤256) (hA : A.length≤4) (hs : Stored m p L)
    (hv : ∀i<A.length,vword v i=zw (A.getD i 0)) :
    Stored (m.write (coeffAddr p L.length) 16 v) p (L++A) := by
  intro i hi
  have hil : i<L.length+A.length:=by simpa only [List.length_append] using hi
  rw [coeffAt_write16 _ _ hL _ (by omega)]
  by_cases hbefore : i<L.length
  · rw [ite_eq_right (by omega),hs i hbefore]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hbefore]
  · rw [ite_eq_left (by omega),hv _ (by omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : L.length≤i)]

theorem storeAccepted_ok {s : State} {p : Addr} {L A : List Zq}
    (hL : L.length+4≤256) (hA : A.length≤4) (hs : Stored s.mem p L)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (hw : InRegions s.wr (coeffAddr p L.length) 16)
    (hv : ∀i<A.length,vword (s.v .v1) i=zw (A.getD i 0)) :
    WP isa (.block [.strq .v1 .x3 0]) s fun t=>
      VG.Proof.MlKem.AArch64.Keep [] s t ∧ t.gpr=s.gpr ∧ t.v=s.v ∧
      Frame [polyR p] s.mem t.mem ∧ Stored t.mem p (L++A) := by
  refine VG.Proof.MlKem.AArch64.wp_strq (by decide) (by simpa using h3) hw fun t ht=>
    VG.Proof.MlKem.AArch64.wp_nil ?_
  refine ⟨ht.keep,ht.gpr,ht.v,?_,?_⟩
  · rw [ht.mem]
    exact (Frame.refl [polyR p] s.mem).write (by simp) _
      (VG.Proof.MlDsa.AArch64.Arith.Neon.vector_contains p hL)
  · rw [ht.mem]
    exact stored_append_vector hL hA hs hv

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
