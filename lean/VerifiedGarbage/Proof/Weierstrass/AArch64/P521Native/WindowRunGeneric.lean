module

-- separate module: this consolidated proof replays 2.21s of elaboration/kernel work versus 0.45s importing its dependencies (local Lean trace); retaining the boundary avoids replaying it in its sole importer.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowRun
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowGroup
public import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowAffineGroup
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

 def windowDoublesF {F : Type _} [Lean.Grind.CommRing F] : Nat → (F×F×F) → (F×F×F)
  | 0,A => A
  | n+1,A => let D := windowDoublesF n A; dblJF D.1 D.2.1 D.2.2

 def windowNonfinalF {F : Type _} [Lean.Grind.CommRing F] [DecidableEq F] (E : Nat → F×F×F) :
    Nat → (F×F×F) → (F×F×F)
  | 0,A => A
  | j+1,A => windowNonfinalF E j (windowSelectF (windowDoublesF 5 A) (E (j+1)))

 theorem window_doubles_group {C : Curve} (law : Law C) (ha : AM3 C)
    {P : Point C} (hP : onCurve C P=true) (e n : Nat) {A : Fe C×Fe C×Fe C}
    (current : InvJ C A.1 A.2.1 A.2.2 (mul e P)) :
    InvJ C (windowDoublesF n A).1 (windowDoublesF n A).2.1 (windowDoublesF n A).2.2 (mul (2^n*e) P) := by
  induction n with
  | zero => simpa only [windowDoublesF,Nat.pow_zero,Nat.one_mul] using current
  | succ n ih =>
    have doubled := InvJ.dbl law ha (law.onCurve_mul hP (2^n*e)) ih
    rw [law.add_mul_mul hP] at doubled
    have same : 2^n*e+2^n*e=2^(n+1)*e := by rw [Nat.pow_succ,Nat.mul_two,Nat.add_mul]
    rw [same] at doubled
    exact doubled

 theorem window_nonfinal_group {C : Curve} (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {k J : Nat} (hk : k<C.n) (E : Nat → Fe C×Fe C×Fe C)
    (entries : ∀j,1≤j → j<J → InvJ C (E j).1 (E j).2.1 (E j).2.2
      (Window5.winPt C P (k+16*Window5.geom J) j))
    (affine : ∀j,1≤j → j<J → (E j).2.2=0 ∨ (E j).2.2=1) :
    ∀(n : Nat) (A : Fe C×Fe C×Fe C),n<J →
      InvJ C A.1 A.2.1 A.2.2 (mul (Window5.winE (k+16*Window5.geom J) J (n+1)) P) →
      InvJ C (windowNonfinalF E n A).1 (windowNonfinalF E n A).2.1 (windowNonfinalF E n A).2.2
        (mul (Window5.winE (k+16*Window5.geom J) J 1) P)
  | 0,A,_,current => current
  | n+1,A,top,current => by
    let e := Window5.winE (k+16*Window5.geom J) J (n+2)
    have doubled := window_doubles_group law ha hP e 5 current
    change InvJ C (windowDoublesF 5 A).1 (windowDoublesF 5 A).2.1 (windowDoublesF 5 A).2.2 (mul (32*e) P) at doubled
    have hQ := law.onCurve_mul hP (32*e)
    have hS := Window5.onCurve_winPt law hP (k+16*Window5.geom J) (n+1)
    have different : mul (32*e) P≠.infinity → Window5.winPt C P (k+16*Window5.geom J) (n+1)≠.infinity →
        mul (32*e) P≠Window5.winPt C P (k+16*Window5.geom J) (n+1) := by
      intro hQ0 _
      have he : 1≤e := by
        by_contra h
        have e0 : e=0 := by omega_arith
        rw [e0,Nat.mul_zero,Window5.mul_zero_pt] at hQ0
        exact hQ0 rfl
      exact (window_noexc_nonfinal law order hP nonzero hn hk top (by omega_arith) he).1
    have step := window_select_group law ha (A:=windowDoublesF 5 A) (E:=E (n+1)) hQ hS doubled
      (entries (n+1) (by omega_arith) top) (affine (n+1) (by omega_arith) top) different
    have w := Window5.win_add law hP (k:=k+16*Window5.geom J) (J:=J) (j:=n+1) (Nat.le_add_left _ _) top
    change Spec.Weierstrass.add (mul (32*e) P) (Window5.winPt C P (k+16*Window5.geom J) (n+1))=_ at w
    rw [w] at step
    exact window_nonfinal_group law ha order hP nonzero hn hk E entries affine n _ (by omega_arith) step

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

 theorem window_five_generic (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowFiveValue A=windowDoublesF 5 A := rfl

 theorem window_affine_generic (m : Mem) (table : Addr) (k j : Nat) :
    windowAffine m table k j=windowAffineN fieldPrime m table k j := rfl

 theorem window_run_generic (m : Mem) (table : Addr) (k n : Nat) (A : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) :
    windowNonfinal m table k n A=windowNonfinalF (fun j => windowAffineN fieldPrime m table k j) n A := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [windowNonfinal,windowNonfinalF,ih,windowStepValue,window_five_generic,window_affine_generic]

 theorem window_run_group_transfer {C : Curve} {p : Nat} [NeZero p]
    (hp : C.p=p) (law : Law C) (ha : AM3 C) (order : PrimeOrder C)
    {P : Point C} (hP : onCurve C P=true) (nonzero : P≠.infinity) (hn : 64≤C.n)
    {k steps : Nat} (hk : k<C.n) (hSteps : steps<105) (m : Mem) (table : Addr)
    {AX AY AZ OX OY OZ : Nat}
    (value : (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=
      windowNonfinalF (fun j => windowAffineN p m table (k+16*Window5.geom 105) j) steps
        (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ))
    (canonical : ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d+72) 9<C.p)
    (entries : ∀d,1≤d → d≤16 → Rep C (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d) 9))
      (Fin.ofNat C.p (wordsVal m table (lookupEntryOffset d+72) 9)) 1 (mul d P))
    (current : InvJ C (Fin.ofNat C.p AX) (Fin.ofNat C.p AY) (Fin.ofNat C.p AZ)
      (mul (Window5.winE (k+16*Window5.geom 105) 105 (steps+1)) P)) :
    InvJ C (Fin.ofNat C.p OX) (Fin.ofNat C.p OY) (Fin.ofNat C.p OZ)
      (mul (Window5.winE (k+16*Window5.geom 105) 105 1) P) := by
  rcases C with ⟨q,a,b,gx,gy,n,len,qnz,nnz⟩
  dsimp only at hp
  subst q
  let E := fun j => windowAffineN p m table (k+16*Window5.geom 105) j
  have reps (j : Nat) := window_affine_repA law m table (k+16*Window5.geom 105) j canonical entries
  have invs : ∀j,1≤j → j<105 → InvJ _ (E j).1 (E j).2.1 (E j).2.2
      (Window5.winPt _ P (k+16*Window5.geom 105) j) := by
    intro j _ _
    exact InvJ.of_rep01 (reps j).1 (reps j).2
  have zs : ∀j,1≤j → j<105 → (E j).2.2=0 ∨ (E j).2.2=1 := by
    intro j _ _
    exact (reps j).2.symm
  change (Fin.ofNat p OX,Fin.ofNat p OY,Fin.ofNat p OZ)=
    windowNonfinalF E steps (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ) at value
  have result := window_nonfinal_group law ha order hP nonzero hn hk E invs zs steps
    (Fin.ofNat p AX,Fin.ofNat p AY,Fin.ofNat p AZ) hSteps current
  rw [←value] at result
  exact result

end VG.Proof.Weierstrass.AArch64.P521Native
