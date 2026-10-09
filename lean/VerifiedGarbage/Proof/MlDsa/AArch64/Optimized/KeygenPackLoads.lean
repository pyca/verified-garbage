import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoad
import VerifiedGarbage.Proof.Framework.Range

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack

def regAt (j : Nat) : VReg := if j=0 then .v0 else if j=1 then .v1 else if j=2 then .v2 else .v3

theorem regAt_small {j : Nat} : regAt j∈[VReg.v0,.v1,.v2,.v3] := by
  unfold regAt
  split_ifs <;> simp

theorem regAt_reserved {j : Nat} : regAt j∉[VReg.v4,.v16,.v17] := by
  unfold regAt
  split_ifs <;> decide

theorem regAt_distinct {i j : Nat} (hi : i<4) (hj : j<4) (hne : i≠j) : regAt i≠regAt j := by
  dsimp only [regAt]
  split_ifs <;> first | decide | omega

def loadCode (signed : Bool) (j : Nat) : List Instr :=
  .ldrq (regAt j) .x0 (16*j) :: (if signed then convert (regAt j) else [])

theorem loadCount_ok (signed : Bool) (b count : Nat) (hn : count≤4) (s : State)
    (hc : signed=true → Constants b s)
    (hin : ∀j<count,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block ((List.range count).flatMap (loadCode signed))) s fun t =>
      VChg [.v0,.v1,.v2,.v3,.v4] s t ∧ (signed=true → Constants b t) ∧
      ∀j<count,∀e<4,vword (t.v (regAt j)) e=
        if signed then encoded b (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
        else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e := by
  let I := fun n t=>VChg [.v0,.v1,.v2,.v3,.v4] s t ∧ (signed=true → Constants b t) ∧
    ∀j<n,∀e<4,vword (t.v (regAt j)) e=
      if signed then encoded b (vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e)
      else vword (s.mem.read (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16) e
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht=>?_) count (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hct,hvals⟩
    rw [loadCode,←List.append_nil (if signed then convert (regAt j) else [])]
    refine loadOne_ok signed b regAt_reserved hct ⟨by omega,by omega⟩ ?_ fun u hu hcu hv => WP.block_nil_iff.mpr ?_
    · simpa only [hk.rd,hk.wr,hk.gpr] using hin j hj
    · refine ⟨(hk.trans hu).mono ?_,hcu,?_⟩
      · intro r hr
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with hr|rfl|rfl
        · simpa using hr
        · exact List.mem_append_left [.v4] regAt_small
        · simp
      · intro i hi e he
        by_cases hij : i=j
        · subst i
          rw [hv e he,hk.mem,hk.gpr]
        · have hi' : i<j := by omega
          rw [hu.get (regAt i) (by simp [regAt_distinct (by omega) (by omega) hij,
            show regAt i≠VReg.v4 by have := regAt_reserved (j:=i); simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at this; exact this.1])]
          exact hvals i hi' e he
  · exact ⟨VChg.refl _ _,hc,by intro j hj; omega⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
