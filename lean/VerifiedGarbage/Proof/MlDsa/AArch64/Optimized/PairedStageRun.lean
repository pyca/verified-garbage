module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStage
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlDsa.Arith.Pairs
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads

/-! ### `MlDsa.AArch64.Optimized.PairedStore`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VMem)

def pairStores (stride : Nat) : List (VReg × Nat) :=
  (List.finRange 2).flatMap fun p => (List.finRange 8).map fun j =>
    ((bankRegs p)[j.val],1024*p.val+stride*j.val)

def writePair (v : Values) (base : Addr) (stride : Nat) (m : Mem) : Mem :=
  (List.finRange 2).foldl (fun m p => (List.finRange 8).foldl
    (fun m j => m.write (base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16 ((v p)[j.val])) m) m

theorem writeSlice_pair {s : State} {v : Values} (hv : Banks s v) (base : Addr) (stride : Nat) :
    writeSlice (pairStores stride) base s.v s.mem=writePair v base stride s.mem := by
  simp only [writeSlice,pairStores,List.foldl_flatMap,List.foldl_map,writePair]
  congr 1
  funext m p
  congr 1
  funext m j
  rw [hv p j]

theorem pairStores_mem {stride : Nat} {r : VReg × Nat} : r∈pairStores stride ↔
    ∃p:Fin 2,∃j:Fin 8,r=((bankRegs p)[j.val],1024*p.val+stride*j.val) := by
  simp only [pairStores,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨p,j,hj⟩; exact ⟨p,j,hj.symm⟩
  · rintro ⟨p,j,rfl⟩; exact ⟨p,j,rfl⟩

theorem storePair_ok (stride : Nat) (base : Reg)
    (ho : ∀p:Fin 2,∀j:Fin 8,(1024*p.val+stride*j.val)%16=0 ∧ 1024*p.val+stride*j.val<65536)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} (hv : Banks s v)
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions s.wr (s.gpr base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16)
    (k : ∀t,VMem s t (writePair v (s.gpr base) stride s.mem) → WP isa (.block rest) t Q) :
    WP isa (.block ((pairStores stride).map (fun p => Instr.strq p.1 base p.2)++rest)) s Q := by
  refine store_many_ok _ _ ?_ ?_ fun t ht => k t ?_
  · intro r hr
    obtain ⟨p,j,rfl⟩ := pairStores_mem.mp hr
    exact ho p j
  · intro r hmem
    obtain ⟨p,j,rfl⟩ := pairStores_mem.mp hmem
    exact hr p j
  · rw [writeSlice_pair hv] at ht
    exact ht

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedPackedRoot`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedRoots`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_ldrq)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

/-- Read only the selected pair of immutable root vectors. -/
theorem rootLoads_ok (off : Nat) (ha : off%16=0) (hi : off+16<65536)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hb : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16)
    (k : ∀t,VChg [.v28,.v29] s t →
      t.v .v28=s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16 →
      t.v .v29=s.mem.read (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16 → WP isa (.block rest) t Q) :
    WP isa (.block (rootPair off++rest)) s Q := by
  refine wp_ldrq (by omega_using [ha, hi]) rfl hr fun a h₁ => ?_
  refine wp_ldrq (by omega_using [ha, hi]) rfl ?_ fun t h₂ => ?_
  · simpa only [h₁.rd,h₁.wr,h₁.gpr] using hb
  · refine k t (h₁.chg.trans h₂.chg) ?_ ?_
    · rw [h₂.get .v28,h₁.v]
    · rw [h₂.v,h₁.mem,h₁.gpr]

theorem Banks.roots {s t : State} {v : Values} (h : Banks s v)
    (hc : VChg [.v28,.v29] s t) : Banks t v := by
  intro p j
  rw [hc.get _ ?_,h p j]
  have hs := bank_safe (j := 8*p.val+j.val) (by omega_using [])
  simp only [bankRegs,Vector.getElem_ofFn,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

/-! ## From `PairedPackedBoth.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (packedValues)

def packedBothCode (i j : Fin 8) (len : Nat) : List Instr :=
  VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed (bankRegs 0)[i.val] (bankRegs 0)[j.val] len++
  VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed (bankRegs 1)[i.val] (bankRegs 1)[j.val] len

def packedBothClobs (i j : Fin 8) : List VReg :=
  packedClobs (bankRegs 0) i j++packedClobs (bankRegs 1) i j

theorem packed_readonly (p : Fin 2) (i j : Fin 8) :
    VReg.v28∉packedClobs (bankRegs p) i j ∧
    VReg.v29∉packedClobs (bankRegs p) i j ∧ VReg.v31∉packedClobs (bankRegs p) i j := by
  have hi := bank_safe (j := 8*p.val+i.val) (by omega_using [])
  have hj := bank_safe (j := 8*p.val+j.val) (by omega_using [])
  simp only [packedClobs,bankRegs,Vector.getElem_ofFn,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

theorem packedBoth_ok (i j : Fin 8) (len : Nat) (hij : i≠j)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (packedBothClobs i j) s t →
      Banks t (fun p => packedValues (v p) i j len z) → WP isa (.block rest) t Q) :
    WP isa (.block (packedBothCode i j len++rest)) s Q := by
  unfold packedBothCode
  rw [List.append_assoc]
  refine packedBanks_ok 0 i j len hij hv hz hzw hbw hqw fun a ha hba => ?_
  have hc := packed_readonly 0 i j
  refine packedBanks_ok 1 i j len hij hba hz ?_ ?_ ?_ fun t ht hbt => ?_
  · rw [ha.get .v28 hc.1]; exact hzw
  · rw [ha.get .v29 hc.2.1]; exact hbw
  · rw [ha.get .v31 hc.2.2]; exact hqw
  · refine k t (ha.trans ht) ?_
    intro p
    have hp : p=0 ∨ p=1 := by
      apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      omega_using []
    rcases hp with rfl | rfl
    · simpa only [show (0:Fin 2)≠1 by decide,show (1:Fin 2)≠0 by decide,ite_false,ite_true] using hbt 0
    · simpa only [show (0:Fin 2)≠1 by decide,show (1:Fin 2)≠0 by decide,ite_false,ite_true] using hbt 1

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedPackedRoot.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (packedValues)

structure RootReady (s : State) (off : Nat) (z : Nat → Int) : Prop where
  align : off%16=0
  limit : off+16<65536
  rootRead : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16
  recipRead : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16
  bound : ∀e<4,0≤z e ∧ z e<8380417
  root : ∀e<4,vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 off) 16) e=BitVec.ofInt 32 (z e)
  recip : ∀e<4,vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 (off+16)) 16) e=BitVec.ofInt 32 (reciprocal (z e))

theorem RootReady.chg {s t : State} {off : Nat} {z : Nat → Int} (h : RootReady s off z)
    {rs : List VReg} (hc : VChg rs s t) : RootReady t off z := by
  refine ⟨h.align,h.limit,?_,?_,h.bound,?_,?_⟩
  · rw [hc.rd,hc.wr,hc.gpr]; exact h.rootRead
  · rw [hc.rd,hc.wr,hc.gpr]; exact h.recipRead
  · rw [hc.mem,hc.gpr]; exact h.root
  · rw [hc.mem,hc.gpr]; exact h.recip

def packedRootClobs (i j : Fin 8) : List VReg := [.v28,.v29]++packedBothClobs i j

theorem packedRoot_ok (i j : Fin 8) (len off : Nat) (hij : i≠j)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hr : RootReady s off z)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (packedRootClobs i j) s t →
      Banks t (fun p => packedValues (v p) i j len z) → WP isa (.block rest) t Q) :
    WP isa (.block (rootPair off++packedBothCode i j len++rest)) s Q := by
  rw [List.append_assoc]
  refine rootLoads_ok off hr.align hr.limit hr.rootRead hr.recipRead fun a ha hz hb => ?_
  refine packedBoth_ok i j len hij (hv.roots ha) hr.bound ?_ ?_ ?_ fun t ht hv' => k t (ha.trans ht) hv'
  · rw [hz]; exact hr.root
  · rw [hb]; exact hr.recip
  · rw [ha.get .v31 (by decide)]; exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end

end

/-! ### `MlDsa.AArch64.Optimized.PairedGroupRun`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.PairedGroup`, which only this module used -/

section

/-! ## From `PairedMultiply.lean` -/

@[expose] public section

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

end

end


-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedGroupBank.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PairRegs pairWrites)

def pairValues (v : Vector (BitVec 128) 8) (i j : Fin 8) (z : Nat → Int) : Vector (BitVec 128) 8 :=
  (v.set i.val (VArr.s4.map2 (fun _ a b => a+b) v[i.val] v[j.val])).set j.val
    (fastVector (VArr.s4.map2 (fun _ a b => a-b) v[i.val] v[j.val]) z)
def groupClobs (i j : Fin 8) : List VReg :=
  pairWrites (groupPairs i.val j.val)++(groupProducts j.val).map MulRegs.temp++
    (groupProducts j.val).map MulRegs.dest

theorem groupKeep (p : Fin 2) (i j k : Fin 8) (hki : k≠i) (hkj : k≠j) :
    (bankRegs p)[k.val]∉groupClobs i j := by
  have ht := bank_safe (j := 8*p.val+k.val) (by omega_using [])
  have hn (q : Fin 2) (r : Fin 8) (hkr : k≠r) : vr (8*p.val+k.val)≠vr (8*q.val+r.val) := by
    intro h
    have he := bank_injective (by omega_using []) (by omega_using []) h
    apply hkr
    apply Fin.ext
    omega_using [he]
  have h0i := hn 0 i hki
  have h0j := hn 0 j hkj
  have h1i := hn 1 i hki
  have h1j := hn 1 j hkj
  simp only [bankRegs,Vector.getElem_ofFn,groupClobs,pairWrites,groupPairs,groupProducts,
    PairRegs.writes,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

theorem groupBank_ok (i j : Fin 8) (hij : i≠j)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (groupClobs i j) s t → Banks t (fun p => pairValues (v p) i j z) →
      WP isa (.block rest) t Q) :
    WP isa (.block (batchPair i.val j.val++rest)) s Q := by
  rw [group_code]
  refine batch_ok _ _ (group_shape i j hij) hz hzw hbw hqw fun t hc ht => k t hc ?_
  intro p a
  have hp : ∃r∈groupPairs i.val j.val,r.left=(bankRegs p)[i.val] ∧ r.right=(bankRegs p)[j.val] := by
    have hp' : p=0 ∨ p=1 := by
      apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      omega_using []
    rcases hp' with rfl | rfl
    · exact ⟨⟨vr i.val,vr j.val,.v24⟩,by simp [groupPairs],by simp [bankRegs],by simp [bankRegs]⟩
    · exact ⟨⟨vr (8+i.val),vr (8+j.val),.v25⟩,by simp [groupPairs,Nat.add_comm],by simp [bankRegs],by simp [bankRegs]⟩
  obtain ⟨r,hr,hri,hrj⟩ := hp
  have hh := ht r hr
  rw [hri,hrj,hv p i,hv p j] at hh
  simp only [pairValues,Vector.getElem_set]
  by_cases haj : a=j
  · subst a
    simp only [ite_true]
    exact hh.2
  · have haj' : j.val≠a.val := fun h => haj (Fin.ext h).symm
    simp only [haj',ite_false]
    by_cases hai : a=i
    · subst a
      simp only [ite_true]
      exact hh.1
    · have hai' : i.val≠a.val := fun h => hai (Fin.ext h).symm
      simp only [hai',ite_false]
      rw [hc.get _ (groupKeep p i j a hai haj),hv p a]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def groupRegs : List VReg := (List.range 16).map vr++[.v24,.v25,.v26,.v27]
def groupCode (ps : List (Fin 8 × Fin 8)) : List Instr := ps.flatMap fun (i,j) => batchPair i.val j.val

def groupValues (v : Vector (BitVec 128) 8) (z : Nat → Int) : List (Fin 8 × Fin 8) → Vector (BitVec 128) 8
  | [] => v
  | (i,j)::ps => groupValues (pairValues v i j z) z ps

theorem group_subset (i j : Fin 8) : groupClobs i j⊆groupRegs := by
  exact (show ∀i j:Fin 8,groupClobs i j⊆groupRegs by decide) i j

theorem groupRun_ok (ps : List (Fin 8 × Fin 8)) (hn : ∀p∈ps,p.1≠p.2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg groupRegs s t → Banks t (fun p => groupValues (v p) z ps) →
      WP isa (.block rest) t Q) :
    WP isa (.block (groupCode ps++rest)) s Q := by
  induction ps generalizing s v with
  | nil => exact k s (VChg.refl _ _) hv
  | cons op ps ih =>
    simp only [groupCode,List.flatMap_cons,List.append_assoc]
    refine groupBank_ok op.1 op.2 (hn op (by simp)) hv hz hzw hbw hqw fun a ha va => ?_
    have hc : VChg groupRegs s a := ha.mono (group_subset _ _)
    refine ih (fun p hp => hn p (List.mem_cons_of_mem _ hp)) va ?_ ?_ ?_ fun t ht vt => ?_
    · rw [hc.get .v28 (by decide)]; exact hzw
    · rw [hc.get .v29 (by decide)]; exact hbw
    · rw [hc.get .v31 (by decide)]; exact hqw
    · exact k t ((hc.trans ht).mono (by simp)) vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

end


/-! ## From `PairedStage.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Proof.MlDsa.Pairs

def stagePairs (i : Fin 7) : List (Fin 8 × Fin 8) :=
  match i.val with
  | 0 => [(0,1)]
  | 1 => [(2,3)]
  | 2 => [(4,5)]
  | 3 => [(6,7)]
  | 4 => [(0,2),(1,3)]
  | 5 => [(4,6),(5,7)]
  | _ => [(0,4),(1,5),(2,6),(3,7)]

theorem stagePairs_ne (i : Fin 7) : ∀p∈stagePairs i,p.1≠p.2 := by
  exact (show ∀i:Fin 7,∀p∈stagePairs i,p.1≠p.2 by decide) i

theorem groupValues_eq (v : Vector (BitVec 128) 8) (z : Nat → Int) (ps : List (Fin 8 × Fin 8)) :
    groupValues v z ps = pairsApply (fun a b => (VArr.s4.map2 (fun _ a b => a+b) a b,
      fastVector (VArr.s4.map2 (fun _ a b => a-b) a b) z)) v ps := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih => obtain ⟨i, j⟩ := p; exact ih _

/-- Which pair of stage `i` holds each entry: a finite fact. -/
theorem stagePairs_pairOf : ∀ i : Fin 7, ∀ k : Fin 8,
    (entries (stagePairs i)).Nodup ∧
    pairOf (stagePairs i) k = (if Inverse.leftSide i.val k.val ∨ Inverse.rightSide i.val k.val then
      some (Inverse.leftSource i.val k, Inverse.rightSource i.val k) else none) ∧
    (Inverse.leftSide i.val k.val → Inverse.leftSource i.val k = k) ∧
    (Inverse.rightSide i.val k.val → ¬Inverse.leftSide i.val k.val ∧ Inverse.leftSource i.val k ≠ k) := by
  decide +kernel

/-- The paired in-place scheduling has the same logical bank transition as
    the already verified register-renamed inverse groups. -/
theorem groupValues_stage (i : Fin 7) (v : Vector (BitVec 128) 8) (z : Nat → Int) :
    groupValues v z (stagePairs i)=Inverse.stageValues i.val v z := by
  refine Vector.ext fun k hk => ?_
  obtain ⟨hd, hp, hl, hr⟩ := stagePairs_pairOf i ⟨k, hk⟩
  rw [groupValues_eq, pairsApply_get _ _ hd ⟨k, hk⟩, hp]
  simp only [Inverse.stageValues, Vector.getElem_ofFn]
  by_cases h1 : Inverse.leftSide i.val k
  · simp only [h1, true_or, ite_true, hl h1]
  · by_cases h2 : Inverse.rightSide i.val k
    · simp only [h1, h2, or_true, ite_true, ite_false, (hr h2).2]
    · simp only [h1, h2, or_self, ite_false]

open VG.Proof.MlKem.AArch64 (VChg)

theorem stage_ok (i : Fin 7) {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Values} {z : Nat → Int} (hv : Banks s v)
    (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg groupRegs s t → Banks t (fun p => Inverse.stageValues i.val (v p) z) →
      WP isa (.block rest) t Q) :
    WP isa (.block (groupCode (stagePairs i)++rest)) s Q := by
  refine groupRun_ok _ (stagePairs_ne i) hv hz hzw hbw hqw fun t ht hvt => k t ht ?_
  simpa only [groupValues_stage] using hvt

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedStageRun.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def stageRunRegs : List VReg := [.v28,.v29]++groupRegs

def stageRunCode (off : Fin 7 → Nat) (is : List (Fin 7)) : List Instr :=
  is.flatMap fun i => rootPair (off i)++groupCode (stagePairs i)

def stageRunValues (v : Vector (BitVec 128) 8) (z : Fin 7 → Nat → Int) :
    List (Fin 7) → Vector (BitVec 128) 8
  | [] => v
  | i::is => stageRunValues (Inverse.stageValues i.val v (z i)) z is

theorem stageRun_ok (is : List (Fin 7)) (off : Fin 7 → Nat) (z : Fin 7 → Nat → Int)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : Banks s v) (hr : ∀i,RootReady s (off i) (z i))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg stageRunRegs s t → Banks t (fun p => stageRunValues (v p) z is) →
      WP isa (.block rest) t Q) :
    WP isa (.block (stageRunCode off is++rest)) s Q := by
  induction is generalizing s v with
  | nil => exact k s (VChg.refl _ _) hv
  | cons i is ih =>
    simp only [stageRunCode,List.flatMap_cons,List.append_assoc]
    refine rootLoads_ok (off i) (hr i).align (hr i).limit (hr i).rootRead (hr i).recipRead
      fun a ha hz hb => ?_
    refine stage_ok i (hv.roots ha) (hr i).bound ?_ ?_ ?_ fun b hbb vb => ?_
    · rw [hz]; exact (hr i).root
    · rw [hb]; exact (hr i).recip
    · rw [ha.get .v31 (by decide)]; exact hq
    have hc : VChg stageRunRegs s b := ha.trans hbb
    refine ih vb (fun j => (hr j).chg hc) ?_ fun t ht vt => ?_
    · rw [hc.get .v31 (by decide)]; exact hq
    · exact k t ((hc.trans ht).mono (by simp)) vt

theorem stageRunValues_all (v : Vector (BitVec 128) 8) (z : Nat → Nat → Int) :
    stageRunValues v (fun i => z i.val) (List.finRange 7)=Inverse.runValues z 0 7 v := by
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
