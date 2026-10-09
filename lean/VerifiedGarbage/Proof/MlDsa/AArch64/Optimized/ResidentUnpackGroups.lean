import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

def groupTemps : List VReg := [.v4,.v5,.v6,.v7,.v24]

structure GroupKeep (s t : State) : Prop where
  gpr : t.gpr=s.gpr
  vec : ∀ v, v∉groupTemps → t.v v=s.v v
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

def groupMem (s : State) (d : Nat) : Nat → Mem
  | 0 => s.mem
  | n+1 => (groupMem s d n).write (s.gpr .x4+BitVec.ofNat 64 (16*n)) 16 (parsedVector s d n)

theorem groupMem_frame (s : State) (d : Nat) {n : Nat} (hn : n≤4) :
    Frame [⟨s.gpr .x4,64⟩] s.mem (groupMem s d n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega)).write (r := ⟨s.gpr .x4,64⟩) (by simp) _ (Offset.contains_base _ (by omega) (by omega))

theorem groupMem_read (s : State) (d : Nat) {n g : Nat} (hn : n≤4) (hg : g<n) :
    (groupMem s d n).read (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16=parsedVector s d g := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [groupMem]
    by_cases he : g=n
    · subst g
      simpa only [Mem.readW,Mem.writeW,Nat.reduceMul,Nat.reduceDiv,BitVec.setWidth_eq] using
        Mem.readW_writeW_self (groupMem s d n) _ 16 (parsedVector s d n) (by decide)
    · rw [Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem GroupKeep.parsed {s t : State} (h : GroupKeep s t) (d g : Nat) :
    parsedVector t d g=parsedVector s d g :=
  parsedVector_congr (h.vec .v0 (by decide)) (h.vec .v1 (by decide))
    (h.vec .v2 (by decide)) (h.vec .v20 (by decide)) (h.vec .v21 (by decide))
    (h.vec .v22 (by decide)) (h.vec .v23 (by decide)) d g

/-- All four unrolled groups preserve their common input vectors and constants;
the only memory writes are the four adjacent sixteen-byte output chunks. -/
theorem groups_ok (s : State) {d n : Nat} (hd : d=18 ∨ d=20) (hn : n≤4)
    (hi : ∀ g<4, s.v Unpack.idxRegs[g]! = gatherIndex d g)
    (hw : ∀ g<4, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (.block ((List.range n).flatMap (Unpack.one d))) s fun t =>
      GroupKeep s t ∧ t.mem=groupMem s d n := by
  induction n with
  | zero =>
    exact WP.block_nil_iff.mpr ⟨⟨rfl,fun _ _ => rfl,rfl,rfl,rfl⟩,rfl⟩
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (ih (by omega)) ?_
    intro a ha
    have hn4 : n<4 := by omega
    have hnidx : Unpack.idxRegs[n]! ∉groupTemps := by
      rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl | rfl | rfl | rfl <;> decide
    have hout : Unpack.outRegs[n]! ∈groupTemps := by
      rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl | rfl | rfl | rfl <;> decide
    refine WP.mono (one_ok a hd hn4 (by rw [ha.1.vec _ hnidx]; exact hi n hn4)
      (by simpa only [ha.1.wr,ha.1.gpr] using hw n hn4)) ?_
    intro t ht
    refine ⟨⟨ht.1.trans ha.1.gpr,?_,ht.2.2.2.1.trans ha.1.rd,
      ht.2.2.2.2.1.trans ha.1.wr,ht.2.2.2.2.2.trans ha.1.sp⟩,?_⟩
    · intro v hv
      have hr : v≠Unpack.outRegs[n]! := by intro he; exact hv (he ▸ hout)
      have h24 : v≠.v24 := by intro he; subst v; exact hv (by decide)
      rw [ht.2.1 v hr h24,ha.1.vec v hv]
    · rw [ht.2.2.1,ha.2,ha.1.gpr,ha.1.parsed]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
