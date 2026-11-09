module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupPoint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowGroup
public import VerifiedGarbage.Proof.Weierstrass.WindowJA
import VerifiedGarbage.Proof.Framework.Omega

/-! Affine table entries and secret signed magnitudes represent the window's point. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass

 def windowAffineN (p : Nat) [NeZero p] (m : Mem) (table : Addr) (k j : Nat) : Fin p×Fin p×Fin p :=
  let d := magH 16 (combWin 5 k j)
  (Fin.ofNat p (windowX m table d),
   Fin.ofNat p (if combWin 5 k j<16 then (p-windowY m table d)%p else windowY m table d),
   Fin.ofNat p (if d=0 then 0 else 1))

 theorem window_comb_five (k j : Nat) : combWin 5 k j=Window5.nib k j := by
  simp only [combWin,Window5.nib]
  rw [Nat.pow_mul]

 theorem window_neg_cast {p y : Nat} [NeZero p] (hy : y<p) :
    Fin.ofNat p ((p-y)%p)=-(Fin.ofNat p y) := by
  apply Fin.ext
  simp only [Fin.val_ofNat,Fin.neg_def,Nat.mod_mod,Nat.mod_eq_of_lt hy]

 theorem window_affine_group {C : Curve} (law : Law C) {P : Point C}
    (m : Mem) (table : Addr) (k j : Nat)
    (canonical : ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d+72) 9<C.p)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d+72) 9)) 1 (mul d P)) :
    Rep C (windowAffineN C.p m table k j).1 (windowAffineN C.p m table k j).2.1
      (windowAffineN C.p m table k j).2.2 (Window5.winPt C P k j) := by
  let v := combWin 5 k j
  let d := magH 16 v
  have hv : v<32 := combWin_lt 5 k j
  have hd : d≤16 := magH_le hv
  have win : Window5.winPt C P k j=if 16≤v then mul (v-16) P else negPt (mul (16-v) P) := by
    rw [Window5.winPt,←window_comb_five]
  by_cases hd0 : d=0
  · have v16 : v=16 := by
      dsimp only [d] at hd0
      unfold magH at hd0
      split at hd0 <;> omega_arith
    have zeroDigit : magH 16 (combWin 5 k j)=0 := hd0
    simp only [windowAffineN,windowX,windowY,zeroDigit,ite_true]
    rw [win]
    change Rep C 0 (Fin.ofNat C.p (if v<16 then (C.p-1)%C.p else 1)) 0
      (if 16≤v then mul (v-16) P else negPt (mul (16-v) P))
    simp only [v16,Nat.lt_irrefl,ite_false,Nat.le_refl,ite_true,Nat.sub_self,Window5.mul_zero_pt]
    exact ⟨rfl,law.one_ne_zero,rfl⟩
  · have h1 : 1≤d := by omega_arith
    have entry := entries d h1 hd
    have zeroDigit : magH 16 (combWin 5 k j)≠0 := hd0
    by_cases negative : v<16
    · have dm : d=16-v := by dsimp only [d]; unfold magH; rw [ite_eq_right (by omega_arith)]
      have nc := window_neg_cast (canonical d h1 hd)
      have negEntry := entry.negY
      rw [windowAffineN,win]
      simp only [windowX,windowY,zeroDigit,ite_false]
      change Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
        (Fin.ofNat C.p (if v<16 then (C.p-wordsVal m table (lookupEntryOffset d+72) 9)%C.p
          else wordsVal m table (lookupEntryOffset d+72) 9)) 1
        (if 16≤v then mul (v-16) P else negPt (mul (16-v) P))
      rw [ite_eq_left negative,ite_eq_right (by omega_arith),nc,←dm]
      exact negEntry
    · have dm : d=v-16 := by dsimp only [d]; unfold magH; rw [ite_eq_left (by omega_arith)]
      rw [windowAffineN,win]
      simp only [windowX,windowY,zeroDigit,ite_false]
      change Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
        (Fin.ofNat C.p (if v<16 then (C.p-wordsVal m table (lookupEntryOffset d+72) 9)%C.p
          else wordsVal m table (lookupEntryOffset d+72) 9)) 1
        (if 16≤v then mul (v-16) P else negPt (mul (16-v) P))
      rw [ite_eq_right negative,ite_eq_left (by omega_arith),←dm]
      exact entry

 theorem window_affine_normalized {p : Nat} [NeZero p] (m : Mem) (table : Addr) (k j : Nat) :
    (windowAffineN p m table k j).2.2=1 ∨ (windowAffineN p m table k j).2.2=0 := by
  by_cases h : magH 16 (combWin 5 k j)=0
  · right; simp only [windowAffineN,h,ite_true]; rfl
  · left; simp only [windowAffineN,h,ite_false]; rfl

 theorem window_affine_repA {C : Curve} (law : Law C) {P : Point C}
    (m : Mem) (table : Addr) (k j : Nat)
    (canonical : ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d+72) 9<C.p)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d+72) 9)) 1 (mul d P)) :
    RepA C (windowAffineN C.p m table k j).1 (windowAffineN C.p m table k j).2.1
      (windowAffineN C.p m table k j).2.2 (Window5.winPt C P k j) :=
  ⟨window_affine_group law m table k j canonical entries,window_affine_normalized m table k j⟩

end VG.Proof.Weierstrass.AArch64.P521Native
