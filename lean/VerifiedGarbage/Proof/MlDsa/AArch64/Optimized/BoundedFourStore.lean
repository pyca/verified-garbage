import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCompact
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.Sample.Mem

/-! ## From `BoundedFourValues.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices vectorVal)

/-- Reduction and compaction preserve every accepted value, with no assumptions
about the ignored lanes that are subsequently overwritten by the parser. -/
theorem valueCompact_ok {η mask : Nat} (hη : η=2∨η=4) (hm : mask<16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h13 : ∀e<4,vword (s.v .v18) e=13#32)
    (h5 : ∀e<4,vword (s.v .v19) e=5#32)
    (hq : ∀e<4,vword (s.v .v21) e=8380417#32)
    (heta : ∀e<4,vword (s.v .v20) e=BitVec.ofNat 32 (Spec.MlDsa.q+η))
    (h6 : s.v .v6=shuffleWord mask)
    (hn : ∀e<4,(vword (s.v .v1) e).toNat<16)
    (k : ∀t,VChg [.v1,.v2] s t →
      (∀i<(acceptedIndices mask).length,vword (t.v .v1) i=
        BitVec.ofNat 32 (Spec.MlDsa.ofInt (VG.Proof.MlDsa.Sample.rbC η
          (vword (s.v .v1) (acceptedIndices mask)[i]!).toNat)).val) →
      WP isa (.block rest) t Q) :
    WP isa (.block (vectorVal η++(.vop (.tbl .v1 .v1 .v6)::rest))) s Q := by
  refine vectorVal_ok η h13 h5 hq heta fun a ha hv=>?_
  refine compact_ok hm (by rw [ha.get .v6]; exact h6) fun t ht hc=>?_
  refine k t ((ha.trans ht).mono (by decide)) ?_
  intro i hi
  rw [hc i hi,hv _ (index_bound mask hm i hi)]
  have hh:=valueWord_eq hη (hn _ (index_bound mask hm i hi))
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using hh

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourStore.lean` -/

section

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

end
