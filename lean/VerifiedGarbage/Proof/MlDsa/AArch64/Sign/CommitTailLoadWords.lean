import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailLoadPair

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (low pair_low pair_high)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3 (laneAddr)

structure Loaded (s : State) (r : Reg) (start n : Nat) (t : State) : Prop where
  keep : RegKeep [] s t
  mem : t.mem=s.mem
  lanes : ∀i<25, low t (vreg i)=if start≤i ∧ i<start+2*n
    then s.mem.readW (laneAddr (s.gpr r) (i-start)) 64 else low s (vreg i)

/-- Loads either μ or the packed commitment prefix, keeping the other lanes. -/
theorem loadWords_ok {s : State} {r : Reg} (start n : Nat) (hn : start+2*n≤25)
    (hin : ∀j<n, InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block ((List.range n).flatMap fun j =>
      ([.ldrq (vreg (start+2*j)) r (16*j),
        .vop (.ext (vreg (start+2*j+1)) (vreg (start+2*j)) (vreg (start+2*j)) 8)] : List Instr)))
      s (Loaded s r start n) := by
  refine wp_range_flatMap (M:=isa) (Loaded s r start) (fun j t hj ht => ?_) n
    (Nat.le_refl _) s ⟨RegKeep.refl _ _,rfl,?_⟩
  · have hin' : InRegions (t.rd++t.wr) (t.gpr r+BitVec.ofNat 64 (16*j)) 16 := by
      rw [ht.keep.rd,ht.keep.wr,ht.keep.gpr r (by simp)]
      exact hin j hj
    refine WP.mono (loadPair_ok (j:=start+2*j) (by omega) ⟨by omega,by omega⟩ hin')
      fun u ⟨hu,hmu,hlu⟩ => ⟨(ht.keep.trans hu).mono (by simp),hmu.trans ht.mem,?_⟩
    intro i hi
    rw [hlu i hi,ht.mem,ht.keep.gpr r (by simp)]
    have hlow := pair_low s.mem (s.gpr r) j
    have hhigh := pair_high s.mem (s.gpr r) j
    change (s.mem.read (s.gpr r+BitVec.ofNat 64 (16*j)) 16).extractLsb' 0 64=_ at hlow
    change (s.mem.read (s.gpr r+BitVec.ofNat 64 (16*j)) 16).extractLsb' 64 64=_ at hhigh
    rw [hlow,hhigh]
    by_cases he1 : i=start+2*j+1
    · subst i
      rw [ite_eq_left rfl,ite_eq_left (by omega),show start+2*j+1-start=2*j+1 by omega]
    · rw [ite_eq_right he1]
      by_cases he0 : i=start+2*j
      · subst i
        rw [ite_eq_left rfl,ite_eq_left (by omega),show start+2*j-start=2*j by omega]
      · rw [ite_eq_right he0,ht.lanes i hi]
        have he : (start≤i ∧ i<start+2*j)↔(start≤i ∧ i<start+2*(j+1)) := by omega
        simp only [he]
  · intro i hi
    rw [ite_eq_right (by omega)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
