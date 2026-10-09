import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCompact

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
