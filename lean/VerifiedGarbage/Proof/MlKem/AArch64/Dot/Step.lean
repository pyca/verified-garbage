module

public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Bounds
public import VerifiedGarbage.Proof.MlKem.PolyContract

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Gather
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Contract

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Store.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def interleave (A B : Nat → Nat) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (if i % 2 = 0 then A (i/2) else B (i/2))

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Term.lean`, which only this module imported.

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Pointer.lean`, which only this module imported.

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/FullTerm.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def Accum (s : State) (a : Nat → Sums) : Prop :=
  Lanes (s.v .v21) (fun e => (a e).even) ∧
  Lanes (s.v .v22) (fun e => (a e).odd) ∧
  Lanes (s.v .v23) (fun e => (a e).cross)

def advance (a : Nat → Sums) (F G : Nat → Nat) : Nat → Sums :=
  fun e => (a e).next (F (2*e)) (F (2*e+1)) (G (2*e)) (G (2*e+1))

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Terms.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def sumTerms (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat)
    (a : Nat → Sums) : Nat → Sums :=
  terms.foldl (fun a fg => advance a (F fg) (G fg)) a

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Init.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def zeroSums : Nat → Sums := fun _ => ⟨0,0,0⟩
theorem zeroLanes : Lanes 0 (fun _ => 0) := by
  intro e he
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem sumTerms_bound (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {a : Nat → Sums} {n : Nat} (ha : ∀ e < 4, (a e).Bounded n)
    (hF : ∀ fg ∈ terms, ∀ e < 8, F fg e < 3329)
    (hG : ∀ fg ∈ terms, ∀ e < 8, G fg e < 3329) :
    ∀ e < 4, (sumTerms terms F G a e).Bounded (n+terms.length) := by
  induction terms generalizing a n with
  | nil => simpa only [sumTerms, List.foldl_nil, List.length_nil, Nat.add_zero] using ha
  | cons fg terms ih =>
    have hb : ∀ e < 4, (advance a (F fg) (G fg) e).Bounded (n+1) := fun e he =>
      (ha e he).next (hF fg (by simp) _ (by omega)) (hF fg (by simp) _ (by omega))
        (hG fg (by simp) _ (by omega)) (hG fg (by simp) _ (by omega))
    have hr := ih hb (fun fg hf => hF fg (by simp [hf])) (fun fg hf => hG fg (by simp [hf]))
    simpa only [sumTerms, List.foldl_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 terms.length] using hr

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Compute.lean`, which only this module imported.
section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

theorem only_vchg {s s' : State} {rs : List VReg} (h : VChg rs s s')
    (hp : ∀ r ∈ preservedV, r ∉ rs := by decide +kernel) : Only [] s s' :=
  ⟨fun _ _ => congrFun h.gpr _, h.mem, h.rd, h.wr, h.sp,
    fun r hr => by rw [h.get r (hp r hr)]⟩

end VG.Proof.MlKem.AArch64.Dot
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Dot/Advance.lean`, which only this module imported.
section

@[expose] public section
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

abbrev clob : List Reg := [.x0,.x1,.x2,.x3,.x9,.x10,.x11,.x12]

def evenResult (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) : Nat → Nat :=
  fun e => ((sumTerms terms F G zeroSums e).even + (sumTerms terms F G zeroSums e).odd * Γ e) % 3329

def oddResult (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) : Nat → Nat :=
  fun e => (sumTerms terms F G zeroSums e).cross % 3329

end VG.Proof.MlKem.AArch64.Dot
