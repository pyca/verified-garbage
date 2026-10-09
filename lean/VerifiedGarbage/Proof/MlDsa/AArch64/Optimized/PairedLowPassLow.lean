import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPassHigh

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The complete r0 pass writes the original-input signed low result at every slot. -/
theorem lowPass_read_low (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : LowIndex) (h : Fin 2)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d n).mem.read (lowAddr (aux+BitVec.ofNat 64 (16*k)) i h) 16=
      lowLowOutput g d.mem (lowAddr (out+BitVec.ofNat 64 (16*k)) i h)
        (lowHalfValue (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 p)) i h) c := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [lowPass_step g work out aux c d (by omega) ho ha,
        lowRun_read_low _ _ _ _ _ _ _ _ _ (allLow_mem i) allLow_nodup (shifted_disjoint out aux _ hd)]
      exact lowLowOutput_read_eq _ _ _ _
        (lowPass_read_future g work out aux c d (Nat.le_refl n) (by omega) i h hd)
    · rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_]
      · exact ih (by omega) (by omega)
      · intro j _
        have h0 := hd.symm.sep (lowAddr_contains aux (by omega : k<8) i h) (lowAddr_contains out (by omega : n<8) j 0)
        have h1 := hd.symm.sep (lowAddr_contains aux (by omega : k<8) i h) (lowAddr_contains out (by omega : n<8) j 1)
        have h2 := lowSlice_sep aux (by omega : n<8) (by omega : k<8) he i j h 0
        have h3 := lowSlice_sep aux (by omega : n<8) (by omega : k<8) he i j h 1
        simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
          And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired
