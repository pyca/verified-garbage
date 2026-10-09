import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckFlags

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def passMask (hint : Bool) (work out : Addr) (c : CheckConstants)
    (m : Mem) (k : Nat) (i : Fin 2 × Fin 8) (e : Nat) : BitVec 32 :=
  checkMask hint ((Inverse.rawFinalValues (readPair m (work+BitVec.ofNat 64 (16*k)) 128 i.1))[i.2.val])
    (m.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16) c e

/-- A final-pass lane accepts exactly when every original coefficient check
accepts, together with its incoming rejection accumulator. -/
theorem finalPass_flag_zero_iff (hint : Bool) (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {n : Nat} (hn : n≤8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) {e : Nat} (he : e<4) :
    vword (finalPassData hint work out aux c d n).flags e=0 ↔
      vword d.flags e=0 ∧ ∀k<n,∀i,passMask hint work out c d.mem k i e=0 := by
  induction n with
  | zero => simp only [finalPassData,Nat.not_lt_zero,false_implies,forall_const,and_true]
  | succ n ih =>
    rw [finalPass_step hint work out aux c d (by omega) hw,
      checkRun_flag_zero_iff _ _ _ _ _ _ _ allChecks_nodup he,ih (by omega)]
    have hlast : (∀i∈allChecks,
        checkMask hint ((Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*n)) 128 i.1))[i.2.val])
          ((finalPassData hint work out aux c d n).mem.read
            (checkAddr (out+BitVec.ofNat 64 (16*n)) i) 16) c e=0) ↔
        ∀i,passMask hint work out c d.mem n i e=0 := by
      simp only [finalPass_read_future hint work out aux c d (Nat.le_refl n) (by omega),
        allChecks_mem,true_implies,passMask]
    rw [hlast]
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
