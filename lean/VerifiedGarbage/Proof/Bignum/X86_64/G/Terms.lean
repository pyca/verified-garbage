import VerifiedGarbage.Proof.Bignum.X86_64.G.ESym

/-!
# RSA with AVX512_IFMA on x86-64, any size: the terms of a step

`AmmTerms` for `CrtIfmaG.ammStep l i`: the terms `ESym.run` computes for
step `i` of a block, written for any `i` and `l` (`expReg`), and checked
against the run for each `i < R` of each layout (`checkStep`).

For each prime `p` (0 or 1, at `D p` from each base): `bT` the limb of the
second operand, broadcast; `a1T` the accumulator of role `k` plus the low
halves of `a b`; `a1hT` plus, for `k ≥ 1`, the high halves of role `k - 1`
of `a b`; `uT` the factor `u`, broadcast; `a2T` plus the low halves of
`u m`; `cT` the carry of role 0's lane 0, in lane 0; `nT` role `k` after the
shift (role `k + 1`, with the carry for role 0, and role 0's lanes moved
down for role `R - 1`); `hT` plus the high halves of `u m` (and, for role
`R - 1`, of `a b`).
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64.AmmSym (G)

variable (l : Lay)

/-- The bytes each base may be loaded from: the operands and the modulus' region. -/
def lim : Reg → Nat := fun b =>
  if b = .r8 then l.D + l.NB else if b = .r9 then l.D + 32 * (l.R - 1) + 8
  else if b = .r10 then l.D + l.NB + 32 else 0

/-- The register number of role `k` of prime `p` at step `i`. -/
def regOf (p k i : Nat) : Nat := l.R * p + (k + i) % l.R

/-- The zero register and the temporary. -/
def zN : Nat := 2 * l.R + 4
def tN : Nat := 2 * l.R + 5

def bT (p i : Nat) : T := .bc (.lane0 (.ld .r9 (l.D * p + 32 * i)))
def a1T (p k i : Nat) : T := .mad false (.reg (regOf l p k i)) (bT l p i) (.ld .r8 (l.D * p + 32 * k))
/-- Role `k` plus the high halves of `a b` of role `k - 1` (for `k ≥ 1`). -/
def a1hT (p k i : Nat) : T :=
  if k = 0 then a1T l p 0 i else .mad true (a1T l p k i) (bT l p i) (.ld .r8 (l.D * p + 32 * (k - 1)))
def uT (p i : Nat) : T := .bc (.mad false .zero (a1T l p 0 i) (.ld .r10 (l.D * p + l.oK0)))
def a2T (p k i : Nat) : T := .mad false (a1hT l p k i) (uT l p i) (.ld .r10 (l.D * p + oM + 32 * k))
def cT (p i : Nat) : T := .low (.shr (a2T l p 0 i) 52)
def nT (p k i : Nat) : T :=
  if k = l.R - 1 then .align (.reg (zN l)) (a2T l p 0 i) 1
  else if k = 0 then .add (a2T l p 1 i) (cT l p i) else a2T l p (k + 1) i
def hT (p k i : Nat) : T :=
  if k = l.R - 1 then
    .mad true (.mad true (nT l p k i) (bT l p i) (.ld .r8 (l.D * p + 32 * k))) (uT l p i)
      (.ld .r10 (l.D * p + oM + 32 * k))
  else .mad true (nT l p k i) (uT l p i) (.ld .r10 (l.D * p + oM + 32 * k))

/-- The role at step `i + 1` of register `r % R`. -/
def roleOf (r i : Nat) : Nat := (r % l.R + l.R - (i + 1) % l.R) % l.R

/-- The terms after step `i`. -/
def expReg (i r : Nat) : T :=
  if r < 2 * l.R then hT l (r / l.R) (roleOf l r i) i
  else if r = 2 * l.R then bT l 0 i else if r = 2 * l.R + 1 then bT l 1 i
  else if r = 2 * l.R + 2 then uT l 0 i else if r = 2 * l.R + 3 then uT l 1 i
  else if r = tN l then cT l 1 i else .reg r

/-- The run of step `i` gives `expReg i` in the 32 registers and loads `rax`. -/
def checkStep (i : Nat) : Bool :=
  match ESym.init.run (lim l) (ammStep l i) with
  | some σ => (List.range 32).all (fun r => decide (σ.reg r = expReg l i r)) &&
      decide (σ.rax = .ld .r9 (l.D + 32 * i))
  | none => false

/-- The layouts the code runs. -/
def LayOk (l : Lay) : Prop := l = lay2048 ∨ l = lay3072 ∨ l = lay4096

theorem checkStep_2048 : ∀ i < lay2048.R, checkStep lay2048 i = true := by decide +kernel
theorem checkStep_3072 : ∀ i < lay3072.R, checkStep lay3072 i = true := by decide +kernel
theorem checkStep_4096 : ∀ i < lay4096.R, checkStep lay4096 i = true := by decide +kernel

theorem checkStep_ok {l : Lay} (hl : LayOk l) : ∀ i < l.R, checkStep l i = true := by
  rcases hl with rfl | rfl | rfl
  · exact checkStep_2048
  · exact checkStep_3072
  · exact checkStep_4096

theorem run_ammStep {l : Lay} (hl : LayOk l) {i : Nat} (hi : i < l.R) :
    ∃ σ, ESym.init.run (lim l) (ammStep l i) = some σ ∧ ∀ r < 32, σ.reg r = expReg l i r := by
  have h := checkStep_ok hl i hi
  unfold checkStep at h
  split at h
  · rename_i σ hσ
    refine ⟨σ, hσ, fun r hr => ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h.1 r hr
  · cases h

end VG.Proof.Bignum.X86_64.G
