import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedMultiply
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePairs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PairRegs pairWrites pairs_ok)

structure BatchShape (ps : List PairRegs) (ms : List MulRegs) : Prop where
  pairs : (ps.flatMap PairRegs.all).Nodup
  multiply : MulShape ms .v28 .v29 .v31
  rootPairs : .v28∉pairWrites ps
  recipPairs : .v29∉pairWrites ps
  qPairs : .v31∉pairWrites ps
  sums : ∀p∈ps,p.left∉ms.map MulRegs.temp++ms.map MulRegs.dest
  products : ∀p∈ps,∃m∈ms,m.source=p.free ∧ m.dest=p.right

/-- Complete paired inverse butterflies. The renamed low-product destinations
are the original right inputs; sums and all read-only constants survive. -/
theorem batch_ok (ps : List PairRegs) (ms : List MulRegs) (h : BatchShape ps ms)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (pairWrites ps++ms.map MulRegs.temp++ms.map MulRegs.dest) s t →
      (∀p∈ps,t.v p.left=VArr.s4.map2 (fun _ a b => a+b) (s.v p.left) (s.v p.right) ∧
        t.v p.right=fastVector (VArr.s4.map2 (fun _ a b => a-b) (s.v p.left) (s.v p.right)) z) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ps.flatMap PairRegs.code++renamedMultiply ms .v28 .v29 .v31++rest)) s Q := by
  rw [List.append_assoc]
  refine pairs_ok ps h.pairs fun a ha hv => ?_
  refine renamedMultiply_ok ms .v28 .v29 .v31 h.multiply hz ?_ ?_ ?_ fun t ht hm => ?_
  · rw [ha.get .v28 h.rootPairs]
    exact hzw
  · rw [ha.get .v29 h.recipPairs]
    exact hbw
  · rw [ha.get .v31 h.qPairs]
    exact hqw
  · refine k t ((ha.trans ht).mono ?_) ?_
    · intro r hr
      simpa only [List.mem_append,or_assoc] using hr
    · intro p hp
      constructor
      · rw [ht.get p.left (h.sums p hp)]
        exact (hv p hp).1
      · obtain ⟨m,hmem,hs,hd⟩ := h.products p hp
        apply vec_ext
        intro e he
        rw [← hd,hm m hmem e he,hs,(hv p hp).2,fastVector_word _ _ he,hd]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
