import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePairs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired

/-! ## From `PairedMultiply.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

/-- The paired schedule keeps differences in temporary registers while
writing the low products directly to their final butterfly destinations. -/
structure MulRegs where
  source : VReg
  dest : VReg
  temp : VReg

def renamedMultiply (ms : List MulRegs) (zr br qr : VReg) : List Instr :=
  ms.map (fun m => .vop (.sqdmulh m.temp m.source br)) ++
  ms.map (fun m => .vop (.mul m.dest m.source zr)) ++
  ms.map (fun m => .vop (.mls m.dest m.temp qr))

structure MulShape (ms : List MulRegs) (zr br qr : VReg) : Prop where
  dest : (ms.map MulRegs.dest).Nodup
  temp : (ms.map MulRegs.temp).Nodup
  sourceDest : ∀ m∈ms,m.source∉ms.map MulRegs.dest
  sourceTemp : ∀ m∈ms,m.source∉ms.map MulRegs.temp
  tempDest : ∀ m∈ms,m.temp∉ms.map MulRegs.dest
  rootDest : zr∉ms.map MulRegs.dest
  rootTemp : zr∉ms.map MulRegs.temp
  recipTemp : br∉ms.map MulRegs.temp
  qDest : qr∉ms.map MulRegs.dest
  qTemp : qr∉ms.map MulRegs.temp

theorem renamedMultiply_ok (ms : List MulRegs) (zr br qr : VReg)
    (h : MulShape ms zr br qr)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v zr) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v br) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v qr) e=8380417#32)
    (k : ∀t,VChg (ms.map MulRegs.temp++ms.map MulRegs.dest) s t →
      (∀m∈ms,∀e<4,vword (t.v m.dest) e=fastMulWord (vword (s.v m.source) e) (z e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (renamedMultiply ms zr br qr++rest)) s Q := by
  unfold renamedMultiply
  rw [List.append_assoc,List.append_assoc]
  have hc : (ms.map (fun m => (m.source,m.temp))).map Prod.snd=ms.map MulRegs.temp := by simp
  have hd : (ms.map (fun m => (m.dest,m.temp))).map Prod.fst=ms.map MulRegs.dest := by simp
  have heq : ms.map (fun m => Instr.vop (.sqdmulh m.temp m.source br))=
      (ms.map (fun m => (m.source,m.temp))).map (fun p => Instr.vop (.sqdmulh p.2 p.1 br)) := by simp
  rw [heq]
  refine high_phase_ok (ms.map (fun m => (m.source,m.temp))) br
    (by simpa only [hc] using h.temp) (by simpa only [hc] using h.recipTemp) ?_
    hz hbw fun a ha hv => ?_
  · intro p hp
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hp
    simpa only [hc] using h.sourceTemp m hm
  · have ha' : VChg (ms.map MulRegs.temp) s a := by simpa only [hc] using ha
    refine parallel_ok ms MulRegs.dest (fun m => .mul m.dest m.source zr)
      (fun m => VArr.s4.map2 (fun _ x y => x*y) (a.v m.source) (a.v zr)) h.dest ?_
      fun b hb hvb => ?_
    · intro t ht m hm _
      change some (m.dest,VArr.s4.map2 (fun _ x y => x*y) (t.v m.source) (t.v zr))=_
      rw [ht.get m.source (h.sourceDest m hm),ht.get zr h.rootDest]
    · have heq' : ms.map (fun m => Instr.vop (.mls m.dest m.temp qr))=
          (ms.map (fun m => (m.dest,m.temp))).map (fun p => Instr.vop (.mls p.1 p.2 qr)) := by simp
      rw [heq']
      refine reduce_phase_ok (ms.map (fun m => (m.dest,m.temp))) qr
        (by simpa only [hd] using h.dest) (by simpa only [hd] using h.qDest) ?_ fun t hc' hvc => ?_
      · intro p hp
        obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hp
        simpa only [hd] using h.tempDest m hm
      · have hc'' : VChg (ms.map MulRegs.dest) b t := by simpa only [hd] using hc'
        refine k t (((ha'.trans hb).trans hc'').mono ?_) ?_
        · intro r hr
          simp only [List.mem_append] at *
          grind only
        · intro m hm e he
          have hm1 : (m.dest,m.temp)∈ms.map (fun m => (m.dest,m.temp)) := List.mem_map.mpr ⟨m,hm,rfl⟩
          rw [hvc (m.dest,m.temp) hm1,VG.Proof.MlKem.AArch64.vword_mapWords3 _ _ _ _ he,
            hvb m hm,VG.AArch64.vword_map2 _ _ _ he,
            ha'.get m.source (h.sourceTemp m hm),ha'.get zr h.rootTemp,
            hb.get m.temp (h.tempDest m hm),hv (m.source,m.temp) (List.mem_map.mpr ⟨m,hm,rfl⟩) e he,
            hb.get qr h.qDest,ha'.get qr h.qTemp,hzw e he,hqw e he]
          rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedBatch.lean` -/

section

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

end

/-! ## From `PairedGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PairRegs)

def groupPairs (a b : Nat) : List PairRegs :=
  [⟨vr a,vr b,.v24⟩,⟨vr (a+8),vr (b+8),.v25⟩]

def groupProducts (b : Nat) : List MulRegs :=
  [⟨.v24,vr b,.v26⟩,⟨.v25,vr (b+8),.v27⟩]

theorem group_shape (a b : Fin 8) (hab : a≠b) :
    BatchShape (groupPairs a.val b.val) (groupProducts b.val) := by
  constructor
  · revert hab b a; decide +kernel
  · constructor <;> revert hab b a <;> decide +kernel
  · revert hab b a; decide +kernel
  · revert hab b a; decide +kernel
  · revert hab b a; decide +kernel
  · revert hab b a; decide +kernel
  · intro p hp
    simp only [groupPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨⟨.v24,vr b.val,.v26⟩,by simp [groupProducts],rfl,rfl⟩
    · exact ⟨⟨.v25,vr (b.val+8),.v27⟩,by simp [groupProducts],rfl,rfl⟩

theorem group_code (a b : Nat) :
    batchPair a b=(groupPairs a b).flatMap PairRegs.code++renamedMultiply (groupProducts b) .v28 .v29 .v31 := rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
