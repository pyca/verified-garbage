import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePairs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def multiplyCode (ps : List (VReg × VReg)) : List Instr :=
  ps.map (fun p => .vop (.sqdmulh p.2 p.1 .v21)) ++
  (ps.map Prod.fst).map (fun d => .vop (.mul d d .v20)) ++
  ps.map (fun p => .vop (.mls p.1 p.2 .v31))

/-- Register-disjointness certificate for an inverse arithmetic batch.
Every reciprocal multiply consumes the difference from its own input pair. -/
structure BatchShape (ps : List PairRegs) (ms : List (VReg × VReg)) : Prop where
  pairs : (ps.flatMap PairRegs.all).Nodup
  data : (ms.map Prod.fst).Nodup
  temps : (ms.map Prod.snd).Nodup
  dataTemps : ∀ p∈ms, p.1∉ms.map Prod.snd
  tempsData : ∀ p∈ms, p.2∉ms.map Prod.fst
  rootData : .v20∉ms.map Prod.fst
  rootTemps : .v20∉ms.map Prod.snd
  recipTemps : .v21∉ms.map Prod.snd
  qData : .v31∉ms.map Prod.fst
  qTemps : .v31∉ms.map Prod.snd
  rootPairs : .v20∉pairWrites ps
  recipPairs : .v21∉pairWrites ps
  qPairs : .v31∉pairWrites ps
  sums : ∀ p∈ps, p.left∉ms.map Prod.snd ++ ms.map Prod.fst
  products : ∀ p∈ps, ∃ temp, (p.free,temp)∈ms

/-- Complete scheduled inverse batch: independent add/sub pairs followed by
high-product, low-product, and reduction phases. -/
theorem batch_ok (ps : List PairRegs) (ms : List (VReg × VReg)) (hshape : BatchShape ps ms)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀ e<4, 0≤z e ∧ z e<8380417)
    (hzw : ∀ e<4, vword (s.v .v20) e=BitVec.ofInt 32 (z e))
    (hbw : ∀ e<4, vword (s.v .v21) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg (pairWrites ps ++ ms.map Prod.snd ++ ms.map Prod.fst) s t →
      (∀ p∈ps, t.v p.left=VArr.s4.map2 (fun _ a b => a+b) (s.v p.left) (s.v p.right) ∧
        t.v p.free=fastVector (VArr.s4.map2 (fun _ a b => a-b) (s.v p.left) (s.v p.right)) z) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ps.flatMap PairRegs.code ++ multiplyCode ms ++ rest)) s Q := by
  rw [List.append_assoc]
  refine pairs_ok ps hshape.pairs fun a ha hv => ?_
  refine multiply_batch_ok ms .v20 .v21 .v31 hshape.data hshape.temps hshape.dataTemps
    hshape.tempsData hshape.rootData hshape.rootTemps hshape.recipTemps hshape.qData hshape.qTemps
    hz ?_ ?_ ?_ fun t ht hm => ?_
  · rw [ha.get .v20 hshape.rootPairs]
    exact hzw
  · rw [ha.get .v21 hshape.recipPairs]
    exact hbw
  · rw [ha.get .v31 hshape.qPairs]
    exact hqw
  · refine k t (VChg.mono (ha.trans ht) ?_) ?_
    · intro r hr
      simpa only [List.mem_append,or_assoc] using hr
    · intro p hp
      constructor
      · rw [ht.get p.left (hshape.sums p hp)]
        exact (hv p hp).1
      · obtain ⟨temp,hmul⟩ := hshape.products p hp
        apply vec_ext
        intro e he
        rw [hm (p.free,temp) hmul e he,(hv p hp).2,fastVector_word _ _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
