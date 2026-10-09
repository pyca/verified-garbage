import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq coeffAt)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16)

/-- A vector store appends four accepted coefficients without touching an
already accepted prefix. -/
theorem stored_append_four {m : Mem} {p : Addr} {L W : List Zq} {v : BitVec 128}
    (hL : Stored m p L) (hsize : L.length+4≤256) (hlen : W.length=4)
    (hv : ∀e<4,(vword v e).toNat=(W.getD e 0).val) :
    Stored (m.write (coeffAddr p L.length) 16 v) p (L++W) := by
  intro i hi
  have hb : i<256 := by rw [List.length_append,hlen] at hi; omega
  rw [coeffAt_write16 _ _ hsize _ hb]
  by_cases h : i<L.length
  · rw [ite_eq_right (by omega),List.getD_eq_getElem?_getD,List.getElem?_append_left h]
    exact hL i h
  · rw [ite_eq_left (by rw [List.length_append,hlen] at hi; omega),
      List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [zw_toNat]
    exact hv (i-L.length) (by rw [List.length_append,hlen] at hi; omega)

/-- Successful vector acceptance stores all four values in one write and
advances exactly as four scalar acceptances would. -/
theorem vectorAccept_ok {s : State} {p : Addr} {L W : List Zq}
    (hL : Stored s.mem p L) (hsize : L.length+4≤256) (hlen : W.length=4)
    (hv : ∀e<4,(vword (s.v .v1) e).toNat=(W.getD e 0).val)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length)
    (hw : InRegions s.wr (s.gpr .x3) 16) :
    WP isa (.block vectorAccept) s fun t =>
      Keep [.x3,.x4] s t ∧ Frame [polyR p] s.mem t.mem ∧
      t.mem=s.mem.write (s.gpr .x3) 16 (s.v .v1) ∧
      t.gpr .x3=coeffAddr p (L++W).length ∧
      (t.gpr .x4).toNat=256-(L++W).length ∧ Stored t.mem p (L++W) := by
  refine wp_strq (a := s.gpr .x3) (by decide) (ptr_zero _) hw fun a ha =>
    wp_addImm (by decide) fun b hb eb => wp_subImm (by decide) fun t ht et => wp_nil ?_
  have hm : t.mem=s.mem.write (s.gpr .x3) 16 (s.v .v1) := by rw [ht.mem,hb.mem,ha.mem]
  refine ⟨((ha.keep.trans hb.keep).trans ht.keep).mono (by decide),?_,hm,?_,?_,?_⟩
  · rw [hm,h3]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _
      (Offset.contains_base p (by omega) (by omega))
  · rw [ht.get .x3,eb,ha.gpr,h3,List.length_append,hlen,coeffAddr,coeffAddr]
    rw [Offset.add_add]
    congr 1
  · rw [et,hb.get .x4,ha.gpr,toNat_sub_c _ 4 (by decide),h4,List.length_append,hlen,
      ite_eq_left (by omega)]
    omega
  · rw [hm,h3]
    exact stored_append_four hL hsize hlen hv

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
