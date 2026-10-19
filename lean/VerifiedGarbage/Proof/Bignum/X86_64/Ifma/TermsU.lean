module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Terms
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64: the terms of a step with the look-ahead

For `CrtIfma.ammStepU l p i`, lane `p`'s step `i` of `ammCoreU`, the terms
`ESym.run` computes, written for any `p`, `i` and `l` (`expRegU`), and checked
against the run of each step of the layout that uses it (`checkStepU`).

At the step's start, role 0 holds the low halves of `a₀ b_i` already, and
the registers of the step's parity hold `b_i` (`bU`) and `u_i` (`uU`). Role 0
gets the low halves of `u m₀` (`a0U`); `m1U` and `m2U` are `u`'s products
for limb 1; role 1 gets the halves of `a b` for limb 1 (`r1aU`), the next
step's `lo(a₀ b_(i+1))` (`pnU`, unless the step is the last), `m1U`, `m2U`
and role 0's carry (`cU`), and becomes the next role 0 (`r1U`), from which
the next `u` is computed (`kU`); role 0, shifted down a lane, gets the high
halves of the top limbs (`topU`); the other roles get their four products
(`restU`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (G)

variable (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay)

/-- The bytes each base may be loaded from: the operands, the second
operand whole, and the modulus' region. -/
def limU : Reg → Nat := fun b =>
  if b = .r8 then l.D * (l.nl - 1) + l.NB else if b = .r9 then l.D * (l.nl - 1) + l.NB
  else if b = .r10 then l.D * (l.nl - 1) + l.NB + 32 else 0

/-- The look-ahead's register numbers (`ubReg`, `uuReg`, …). -/
def ubN (p par : Nat) : Nat := l.nl * l.R + 8 * p + par
def uuN (p par : Nat) : Nat := l.nl * l.R + 8 * p + 2 + par
def utN (p : Nat) : Nat := l.nl * l.R + 8 * p + 4
def um1N (p : Nat) : Nat := l.nl * l.R + 8 * p + 5
def um2N (p : Nat) : Nat := l.nl * l.R + 8 * p + 6
def upnN (p : Nat) : Nat := l.nl * l.R + 8 * p + 7
def uzN : Nat := l.nl * l.R + 8 * l.nl

def ldA (p k : Nat) : T := .ld .r8 (l.D * p + 32 * k)
def ldM (p k : Nat) : T := .ld .r10 (l.D * p + oM + 32 * k)
def bU (p i : Nat) : T := .reg (ubN l p (i % 2))
def uU (p i : Nat) : T := .reg (uuN l p (i % 2))
def bnU (p i : Nat) : T := .bc (.lane0 (.ld .r9 (l.D * p + l.off (i + 1))))
def a0U (p i : Nat) : T := .mad false (.reg (regOf l p 0 i)) (uU l p i) (ldM l p 0)
def m1U (p i : Nat) : T := .mad false .zero (uU l p i) (ldM l p 1)
def m2U (p i : Nat) : T := .mad true .zero (uU l p i) (ldM l p 0)
def r1aU (p i : Nat) : T :=
  .mad true (.mad false (.reg (regOf l p 1 i)) (bU l p i) (ldA l p 1)) (bU l p i) (ldA l p 0)
def pnU (p i : Nat) : T := .mad false .zero (bnU l p i) (ldA l p 0)
def r1bU (p i : Nat) : T := if l.S ≤ i + 1 then r1aU l p i else .add (r1aU l p i) (pnU l p i)
def cU (p i : Nat) : T := .low (.shr (a0U l p i) 52)
def r1U (p i : Nat) : T := .add (.add (.add (r1bU l p i) (m1U l p i)) (m2U l p i)) (cU l p i)
def kU (p i : Nat) : T := .mad false .zero (r1U l p i) (.ld .r10 (l.D * p + l.oK0))
def tU (p i : Nat) : T := if l.S ≤ i + 1 then cU l p i else kU l p i
def restU (p k i : Nat) : T :=
  .mad true (.mad false (.mad true (.mad false (.reg (regOf l p k i)) (bU l p i) (ldA l p k)) (bU l p i)
    (ldA l p (k - 1))) (uU l p i) (ldM l p k)) (uU l p i) (ldM l p (k - 1))
def topU (p i : Nat) : T :=
  .mad true (.mad true (.align (.reg (uzN l)) (a0U l p i) 1) (bU l p i) (ldA l p (l.R - 1))) (uU l p i)
    (ldM l p (l.R - 1))

/-- The role at step `i` of register `r` of a lane. -/
def roleAt (r i : Nat) : Nat := (r % l.R + l.R - i % l.R) % l.R

/-- The terms after lane `p`'s step `i`. -/
def expRegU (p i r : Nat) : T :=
  if l.R * p ≤ r ∧ r < l.R * p + l.R then
    if roleAt l r i = 0 then topU l p i else if roleAt l r i = 1 then r1U l p i
    else restU l p (roleAt l r i) i
  else if r = ubN l p ((i + 1) % 2) ∧ ¬ l.S ≤ i + 1 then bnU l p i
  else if r = uuN l p ((i + 1) % 2) ∧ ¬ l.S ≤ i + 1 then .bc (kU l p i)
  else if r = utN l p then tU l p i
  else if r = um1N l p then m1U l p i
  else if r = um2N l p then m2U l p i
  else if r = upnN l p ∧ ¬ l.S ≤ i + 1 then pnU l p i
  else .reg r

/-- The run of lane `p`'s step `i` gives `expRegU p i` in the 32 registers,
and loads `rax` but in the last step. -/
def checkStepU (p i : Nat) : Bool :=
  match ESym.init.run (limU l) (ammStepU l p i) with
  | some σ => (List.range 32).all (fun r => T.beq (σ.reg r) (expRegU l p i r)) &&
      (if l.S ≤ i + 1 then G.beq σ.rax (.gpr .rax) else G.beq σ.rax (.ld .r9 (l.D * p + l.off (i + 1))))
  | none => false

theorem checkStepU_2048 : ∀ p < lay2048.nl, ∀ i < lay2048.S, checkStepU lay2048 p i = true := by
  decide +kernel

theorem checkStepU_p2048 : ∀ p < VG.Impl.Rsa.X86_64.PubIfma.pay2048.nl,
    ∀ i < VG.Impl.Rsa.X86_64.PubIfma.pay2048.S, checkStepU VG.Impl.Rsa.X86_64.PubIfma.pay2048 p i = true := by
  decide +kernel

open VG.Impl.Rsa.X86_64.PubIfma (pay2048) in
/-- The layouts whose multiplication has the look-ahead (`ammMul`): 2048
bits, the CRT's and the public operation's. -/
def UOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop := l = lay2048 ∨ l = pay2048

variable {l} in
/-- `ammMul`'s choice: the look-ahead where the roles take at most 10 registers. -/
theorem UOk.of_amm (hl : AmmOk l) (h : l.nl * l.R ≤ 10) : UOk l := by
  rcases hl with (rfl | rfl | rfl) | rfl | rfl | rfl
  · exact .inl rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact .inr rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

variable {l} in
/-- The sizes the proofs of the look-ahead use: two roles or more, the
registers of the roles, the lanes' eight and the zero register. -/
theorem UOk.regs (hu : UOk l) :
    AmmOk l ∧ 2 ≤ l.R ∧ l.R ≤ 20 ∧ 1 ≤ l.nl ∧ l.nl * l.R + 8 * l.nl < 32 := by
  rcases hu with rfl | rfl
  · exact ⟨.inl (.inl rfl), by decide⟩
  · exact ⟨.inr (.inl rfl), by decide⟩

variable {l} in
theorem UOk.checkStep (hu : UOk l) : ∀ p < l.nl, ∀ i < l.S, checkStepU l p i = true := by
  rcases hu with rfl | rfl
  · exact checkStepU_2048
  · exact checkStepU_p2048

variable {l} in
theorem run_ammStepU (hu : UOk l) {p i : Nat} (hp : p < l.nl) (hi : i < l.S) :
    ∃ σ, ESym.init.run (limU l) (ammStepU l p i) = some σ ∧
      (∀ r < 32, σ.reg r = expRegU l p i r) ∧
      σ.rax = (if l.S ≤ i + 1 then .gpr .rax else .ld .r9 (l.D * p + l.off (i + 1))) := by
  have h := hu.checkStep p hp i hi
  unfold checkStepU at h
  split at h
  · rename_i σ hσ
    refine ⟨σ, hσ, fun r hr => ?_, ?_⟩
    · simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
      exact T.eq_of_beq (h.1 r hr)
    · simp only [Bool.and_eq_true] at h
      split at h <;> rename_i hl <;> simp only [hl, ite_true, ite_false] <;> exact G.eq_of_beq h.2
  · cases h

end VG.Proof.Bignum.X86_64.Ifma
