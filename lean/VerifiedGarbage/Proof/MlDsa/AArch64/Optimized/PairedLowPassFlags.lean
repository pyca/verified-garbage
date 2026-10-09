import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPassRead
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRunFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem allLow_mem (i : LowIndex) : i∈allLow := by
  simp only [allLow,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  exact ⟨i.1,i.2,rfl⟩

theorem allLow_nodup : allLow.Nodup := by decide +kernel

def lowPassAccept (g : Nat) (work out : Addr) (c : LowConstants) (m : Mem)
    (e k : Nat) (i : LowIndex) : Prop :=
  lowPairAccept g (fun p => Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*k)) 128 p))
    (out+BitVec.ofNat 64 (16*k)) c m e i

theorem lowPass_flag_zero_iff (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {n : Nat} (hn : n≤8)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    {e : Nat} (he : e<4) :
    vword (lowPassData g work out aux c d n).flags e=0 ↔
      vword d.flags e=0 ∧ ∀k<n,∀i,lowPassAccept g work out c d.mem e k i := by
  induction n with
  | zero => simp only [lowPassData,Nat.not_lt_zero,false_implies,forall_const,and_true]
  | succ n ih =>
    rw [lowPass_step g work out aux c d (by omega) ho ha]
    have hshift : (⟨out+BitVec.ofNat 64 (16*n),2048⟩ : Region).Disjoint
        ⟨aux+BitVec.ofNat 64 (16*n),2048⟩ := by
      intro a hx hy
      exact hd (a-BitVec.ofNat 64 (16*n)) (by
        simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hx)
        (by simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hy)
    rw [lowRun_flag_zero_iff _ _ _ _ _ _ _ allLow_nodup hshift he,ih (by omega)]
    have ht : (∀i∈allLow,lowPairAccept g
        (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
        (out+BitVec.ofNat 64 (16*n)) c (lowPassData g work out aux c d n).mem e i) ↔
        ∀i,lowPassAccept g work out c d.mem e n i := by
      have hp (i : LowIndex) := lowPass_read_future g work out aux c d (Nat.le_refl n) (by omega : n<8) i
      have heq (i : LowIndex) : lowPairAccept g
          (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 p))
          (out+BitVec.ofNat 64 (16*n)) c (lowPassData g work out aux c d n).mem e i ↔
          lowPassAccept g work out c d.mem e n i := by
        have h0 := hp i 0 hd
        have h1 := hp i 1 hd
        simp only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at h0 h1
        unfold lowPassAccept lowPairAccept
        rw [lowMask_read_eq _ _ _ _ _ h0,lowMask_read_eq _ _ _ _ _ h1]
      exact ⟨fun h i => (heq i).mp (h i (allLow_mem i)),fun h i _ => (heq i).mpr (h i)⟩
    rw [ht]
    constructor
    · rintro ⟨⟨h0,hprev⟩,hlast⟩
      refine ⟨h0,fun k hk i => ?_⟩
      by_cases hkn : k<n
      · exact hprev k hkn i
      · have heq : k=n := by omega
        subst k
        exact hlast i
    · rintro ⟨h0,hall⟩
      exact ⟨⟨h0,fun k hk => hall k (by omega)⟩,hall n (by omega)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
