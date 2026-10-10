import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRoots

/-! ## From `PairedPackedBoth.lean` -/

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
  have hi := bank_safe (j := 8*p.val+i.val) (by omega)
  have hj := bank_safe (j := 8*p.val+j.val) (by omega)
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
      omega
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

theorem packedRoot_q (i j : Fin 8) : VReg.v31∉packedRootClobs i j := by
  have h0 := (packed_readonly 0 i j).2.2
  have h1 := (packed_readonly 1 i j).2.2
  simp only [packedRootClobs,packedBothClobs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

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
