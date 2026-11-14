module
public import VerifiedGarbage.Impl.X25519.X86_64.Ifma
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Bound

import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-!
# X25519 on x86-64 with AVX512_IFMA: the stages' operands

The blocks between the carries and the products of an iteration, run
symbolically: each output limb, lane by lane, as a number (`rfl`), and its
bounds (`decide`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519

/-- A block run from its start. -/
def symOf (is : List Instr) (h : (Sym.init.run is).isSome := by decide +kernel) : Sym :=
  (Sym.init.run is).get h

theorem symOf_eq (is : List Instr) (h : (Sym.init.run is).isSome) :
    Sym.init.run is = some (symOf is h) := (Option.some_get _).symm

/-! ## Stage 1 -/

def s1a : Sym := symOf stage1a

/-- `(x₂ + bias - z₂, x₂ + z₂, x₃ + bias - z₃, x₃ + z₃)`, limb `j`. -/
def s1aNat (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 0 + (E.m (kb j) 0 - E.v j 1)
  | 1 => E.v j 0 + E.v j 1
  | 2 => E.v j 2 + (E.m (kb j) 2 - E.v j 3)
  | _ => E.v j 2 + E.v j 3

theorem s1a_nat (E : Env) : ∀ j < 5, ∀ l < 4, (s1a.reg j).nat E l = s1aNat E j l := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- Bounds: limbs below `2⁶¹`, and the bias. -/
def s1aB : Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0, fun _ => 2 ^ 64 - 1⟩

theorem s1a_ok : ∀ j < 5, ∀ l < 4, (s1a.reg j).ok s1aB l = true ∧ (s1a.reg j).bnd s1aB l < 2 ^ 63 := by
  decide +kernel

theorem s1a_keep : ∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → s1a.reg r = .reg r := by decide +kernel
theorem s1a_st : s1a.st = [] := by decide +kernel

def s1b : Sym := symOf stage1b

/-- `vidx`'s index of the first operand, a quadword: the mask's doublewords
below 4, by `K4D`, onto `KIU`'s. -/
def idxU : T := .xor (.and (.reg 15) (.ld K4D)) (.ld KIU)
/-- The second operand's, onto `KIV`'s. -/
def idxV : T := .xor (.and (.reg 15) (.ld K4D)) (.ld KIV)

theorem s1b_regsU : ∀ j < 5, s1b.reg (10 + j) = .pd idxU (.reg j) := by decide +kernel
theorem s1b_regsV : ∀ j < 5, s1b.reg (5 + j) = .pd idxV (.reg j) := by decide +kernel
theorem s1b_st : s1b.st = [] := by decide +kernel
theorem s1b_keep : ∀ r < 5, s1b.reg r = .reg r := by decide +kernel

/-! ## Stage 2 -/

def s2a : Sym := symOf stage2a

/-- `(AA, AA + bias - BB, DA + CB, DA + bias - CB)` from `(BB, AA, CB, DA)`, limb `j`. -/
def s2aU (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 1
  | 1 => E.v j 1 + (E.m (kb j) 1 - E.v j 0)
  | 2 => E.v j 3 + E.v j 2
  | _ => E.v j 3 + (E.m (kb j) 3 - E.v j 2)

theorem s2a_nat (E : Env) : ∀ j < 5, ∀ l < 4, (s2a.reg (10 + j)).nat E l = s2aU E j l := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem s2a_ok : ∀ j < 5, ∀ l < 4, (s2a.reg (10 + j)).ok s1aB l = true ∧
    (s2a.reg (10 + j)).bnd s1aB l < 2 ^ 63 := by
  decide +kernel

theorem s2a_keep : ∀ r < 5, s2a.reg r = .reg r := by decide +kernel
theorem s2a_st : s2a.st = [] := by decide +kernel

def s2b : Sym := symOf stage2b

/-- No bounds: for the blocks that only move quadwords. -/
def topB : Bnds := ⟨fun _ => 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1, fun _ => 0, fun _ => 2 ^ 64 - 1⟩

theorem s2b_nat (E : Env) : ∀ j < 5, ∀ l < 4, (s2b.reg (5 + j)).nat E l =
    if l < 2 then E.m (KA24 + 32 * j) l else E.v (10 + j) l := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl
theorem s2b_ok : ∀ j < 5, ∀ l < 4, (s2b.reg (5 + j)).ok topB l = true := by decide +kernel
theorem s2b_st : s2b.st = [] := by decide +kernel
theorem s2b_keep : ∀ r < 16, (r < 5 ∨ 10 ≤ r) → s2b.reg r = .reg r := by decide +kernel

/-! ## Stage 3 -/

def s3b : Sym := symOf stage3b

theorem s3b_nat (E : Env) : ∀ j < 5, ∀ l < 4,
    (s3b.reg (10 + j)).nat E l = (if l < 2 then E.v (10 + j) l else E.v j l) ∧
    (s3b.reg (5 + j)).nat E l = (if l < 2 then E.v j l else E.m (KX1 + 32 * j) l) := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
theorem s3b_ok : ∀ j < 5, ∀ l < 4, (s3b.reg (10 + j)).ok topB l = true ∧ (s3b.reg (5 + j)).ok topB l = true := by
  decide +kernel
theorem s3b_st : s3b.st = [] := by decide +kernel

/-! ## The mask -/

def mkS : Sym := symOf vmask

theorem mkS_reg : mkS.reg 15 = .bc (.lane0 (.gpr .rcx)) := by decide +kernel
theorem mkS_keep : ∀ r < 15, mkS.reg r = .reg r := by decide +kernel
theorem mkS_st : mkS.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma
