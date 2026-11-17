module

public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.PolyContract
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `MlKem.AArch64.Dot.Bounds`, which this module and modules that import it used -/

section

/-! Bounds for the unreduced accumulators. No arithmetic wraps for at most
four canonical polynomial terms. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot

structure Sums where
  even : Nat
  odd : Nat
  cross : Nat

def Sums.next (s : Sums) (fe fo ge go : Nat) : Sums :=
  ⟨s.even + fe*ge, s.odd + fo*go, s.cross + fe*go + fo*ge⟩

def Sums.Bounded (s : Sums) (n : Nat) : Prop :=
  s.even ≤ n*(3329*3329) ∧ s.odd ≤ n*(3329*3329) ∧ s.cross ≤ 2*n*(3329*3329)

theorem Sums.Bounded.next {s : Sums} {n fe fo ge go : Nat} (h : s.Bounded n)
    (hf : fe < 3329) (ho : fo < 3329) (hg : ge < 3329) (hp : go < 3329) :
    (s.next fe fo ge go).Bounded (n+1) := by
  have a : fe*ge ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt hf) (Nat.le_of_lt hg)
  have b : fo*go ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt ho) (Nat.le_of_lt hp)
  have c : fe*go ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt hf) (Nat.le_of_lt hp)
  have d : fo*ge ≤ 3329*3329 := Nat.mul_le_mul (Nat.le_of_lt ho) (Nat.le_of_lt hg)
  simp only [Sums.Bounded, Sums.next] at *
  bdd_omega

theorem Sums.Bounded.machine {s : Sums} {n : Nat} (h : s.Bounded n) (hn : n ≤ 4) :
    s.even ≤ 4*3329*3329 ∧ s.odd ≤ 4*3329*3329 ∧ s.cross ≤ 8*3329*3329 := by
  change s.even ≤ 4*(3329*3329) ∧ s.odd ≤ 4*(3329*3329) ∧ s.cross ≤ 8*(3329*3329)
  exact ⟨Nat.le_trans h.1 (Nat.mul_le_mul_right _ hn),
    Nat.le_trans h.2.1 (Nat.mul_le_mul_right _ hn),
    Nat.le_trans h.2.2 (Nat.mul_le_mul_right _ (show 2*n ≤ 8 by omega_using [hn]))⟩

theorem Sums.Bounded.noWrap {s : Sums} {n : Nat} (h : s.Bounded n) (hn : n ≤ 4) :
    s.even < 2^31 ∧ s.odd < 2^31 ∧ s.cross < 2^31 := by
  have := h.machine hn
  bdd_omega

end VG.Proof.MlKem.AArch64.Dot

end

end

/-! ### `MlKem.AArch64.Dot.Gather`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64

def loads : List Instr := [.ldrq .v0 .x1 0, .ldrq .v1 .x1 16, .ldrq .v4 .x2 0, .ldrq .v5 .x2 16]

theorem loads_ok {rest : List Instr} {s : State} {Q : State → Prop}
    (hf : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16*i)) 16)
    (hg : ∀ i < 2, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16*i)) 16)
    (k : ∀ s', VChg [.v0, .v1, .v4, .v5] s s' →
      s'.v .v0 = s.mem.read (s.gpr .x1) 16 →
      s'.v .v1 = s.mem.read (s.gpr .x1 + BitVec.ofNat 64 16) 16 →
      s'.v .v4 = s.mem.read (s.gpr .x2) 16 →
      s'.v .v5 = s.mem.read (s.gpr .x2 + BitVec.ofNat 64 16) 16 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loads ++ rest)) s Q := by
  simp only [loads, List.cons_append, List.nil_append]
  refine wp_ldrq (by decide) rfl (hf 0 (by decide)) fun s₁ h₁ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₁.rd, h₁.wr, h₁.gpr]; exact hf 1 (by decide)) fun s₂ h₂ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, h₂.gpr, h₁.gpr]; exact hg 0 (by decide)) fun s₃ h₃ => ?_
  refine wp_ldrq (by decide) rfl (by rw [h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr, h₃.gpr, h₂.gpr, h₁.gpr]; exact hg 1 (by decide)) fun s₄ h₄ => ?_
  refine k s₄ (((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).mono ?_ ?_ ?_ ?_
  · rw [h₄.get .v0, h₃.get .v0, h₂.get .v0, h₁.v]; simp only [BitVec.add_zero]
  · rw [h₄.get .v1, h₃.get .v1, h₂.v, h₁.mem, h₁.gpr]
  · rw [h₄.get .v4, h₃.v, h₂.mem, h₁.mem, h₂.gpr, h₁.gpr]; simp only [BitVec.add_zero]
  · rw [h₄.v, h₃.mem, h₂.mem, h₁.mem, h₃.gpr, h₂.gpr, h₁.gpr]

end VG.Proof.MlKem.AArch64.Dot

end

end

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
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;> rfl

theorem sumTerms_bound (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Nat → Nat}
    {a : Nat → Sums} {n : Nat} (ha : ∀ e < 4, (a e).Bounded n)
    (hF : ∀ fg ∈ terms, ∀ e < 8, F fg e < 3329)
    (hG : ∀ fg ∈ terms, ∀ e < 8, G fg e < 3329) :
    ∀ e < 4, (sumTerms terms F G a e).Bounded (n+terms.length) := by
  induction terms generalizing a n with
  | nil => simpa only [sumTerms, List.foldl_nil, List.length_nil, Nat.add_zero] using ha
  | cons fg terms ih =>
    have hb : ∀ e < 4, (advance a (F fg) (G fg) e).Bounded (n+1) := fun e he =>
      (ha e he).next (hF fg (by simp) _ (by omega_using [he])) (hF fg (by simp) _ (by omega_using [he]))
        (hG fg (by simp) _ (by omega_using [he])) (hG fg (by simp) _ (by omega_using [he]))
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
