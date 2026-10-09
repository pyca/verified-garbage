import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowInputFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowSlice_sep (base : Addr) {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u)
    (i j : LowIndex) (h t : Fin 2) :
    Mem.Sep (lowAddr (base+BitVec.ofNat 64 (16*k)) i h) 16
      (lowAddr (base+BitVec.ofNat 64 (16*u)) j t) 16 := by
  simp only [lowAddr,lowOff,BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Earlier r0 iterations preserve both inputs of every later pair. -/
theorem lowPass_read_future (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {u k : Nat} (hu : u≤k) (hk : k<8) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d u).mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16=
      d.mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16 := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_,ih (by omega)]
    intro j _
    have h0 := lowSlice_sep out (by omega : u<8) hk (by omega : k≠u) i j h 0
    have h1 := lowSlice_sep out (by omega : u<8) hk (by omega : k≠u) i j h 1
    have h2 := hd.sep (lowAddr_contains out hk i h) (lowAddr_contains aux (by omega : u<8) j 0)
    have h3 := hd.sep (lowAddr_contains out hk i h) (lowAddr_contains aux (by omega : u<8) j 1)
    simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
      And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired
