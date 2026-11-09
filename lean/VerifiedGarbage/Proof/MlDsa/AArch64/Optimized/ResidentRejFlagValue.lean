module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourFlags

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (foldedFlags foldedFlags_succ)

theorem foldedFlags_zero (C : Nat → BitVec 64) (n : Nat) :
    foldedFlags C n=0#64 ↔ ∀i<n+1,C i=0#64 := by
  induction n with
  | zero =>
    change C 0=0#64 ↔ ∀i<1,C i=0#64
    constructor
    · intro h i hi
      have hi0 : i=0 := by omega
      subst i
      exact h
    · intro h; exact h 0 (by decide)
  | succ n ih =>
    rw [foldedFlags_succ,BitVec.or_eq_zero_iff,ih]
    constructor
    · rintro ⟨h,hLast⟩ i hi
      by_cases he : i=n+1
      · subst i; exact hLast
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega),h (n+1) (by omega)⟩

theorem foldedFlags_bound (C : Nat → BitVec 64) (n : Nat)
    (hc : ∀i<n+1,(C i).toNat≤256) : (foldedFlags C n).toNat<512 := by
  induction n with
  | zero => change (C 0).toNat<512; have:=hc 0 (by decide); omega
  | succ n ih =>
    rw [foldedFlags_succ,BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 9) (ih (fun i hi => hc i (by omega)))
      (by have:=hc (n+1) (by omega); omega)

theorem smallFlag_status (x : BitVec 64) (hx : x.toNat<512) :
    (x-1#64)>>>63 = if x=0#64 then 1#64 else 0#64 := by
  by_cases hz : x=0#64
  · subst x; decide
  · rw [ite_eq_right hz]
    have hn : x.toNat≠0 := by intro h; exact hz (BitVec.eq_of_toNat_eq h)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_sub,BitVec.toNat_ofNat]
    omega

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
