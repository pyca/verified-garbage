import VerifiedGarbage.Proof.Bignum.X86_64.AmmSym

/-!
# RSA with AVX512_IFMA on x86-64: the terms of a step

The terms `Sym.run` computes for step `i` of a block (`ammStep i`), written
for any `i` (`expReg`), and checked against the run for each `i < 5`
(`run_ammStep`).

For each prime `p` (0 or 1, at `D p` from each base): `bT` the limb of the
second operand, broadcast; `a1` the accumulator of role `k` plus the low
halves of `a b`; `uT` the factor `u`, broadcast; `a2` plus the low halves of
`u m`; `cT` the carry of role 0's lane 0, in lane 0; `nT` role `k` after the
shift (role `k + 1`, with the carry for role 0, and role 0's lanes shifted
down for role 4); `hT` plus the high halves.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma

/-- The bytes each base may be loaded from: the operands and the modulus' region. -/
def lim : Reg → Nat := fun b =>
  if b = .r8 then D + 160 else if b = .r9 then D + 136 else if b = .r10 then D + 192 else 0

/-- The register number of role `k` of prime `p` at step `i`. -/
def regOf (p k i : Nat) : Nat := 5 * p + (k + i) % 5

def bT (p i : Nat) : A := .bc (.lane0 (.ld .r9 (D * p + 32 * i)))
def a1T (p k i : Nat) : A := .mad false (.reg (regOf p k i)) (bT p i) (.ld .r8 (D * p + 32 * k))
def uT (p i : Nat) : A := .bc (.mad false .zero (a1T p 0 i) (.ld .r10 (D * p + oK0)))
def a2T (p k i : Nat) : A := .mad false (a1T p k i) (uT p i) (.ld .r10 (D * p + oM + 32 * k))
def cT (p i : Nat) : A := .blend (.reg 14) (.shr (a2T p 0 i) 52) 3
def nT (p k i : Nat) : A :=
  if k = 4 then .blend (.perm (a2T p 0 i) 57) (.reg 14) 192
  else if k = 0 then .add (a2T p 1 i) (cT p i) else a2T p (k + 1) i
def hT (p k i : Nat) : A :=
  .mad true (.mad true (nT p k i) (bT p i) (.ld .r8 (D * p + 32 * k))) (uT p i) (.ld .r10 (D * p + oM + 32 * k))

/-- The role at step `i + 1` of register `r % 5`. -/
def roleOf (r i : Nat) : Nat := (r % 5 + 5 - (i + 1) % 5) % 5

/-- The terms after step `i`. -/
def expReg (i r : Nat) : A :=
  if r < 10 then hT (r / 5) (roleOf r i) i
  else if r = 10 then bT 0 i else if r = 11 then bT 1 i
  else if r = 12 then uT 0 i else if r = 13 then uT 1 i
  else if r = 15 then cT 1 i else .reg r

/-- The run of step `i` gives `expReg i` in the 16 registers and loads `rax`. -/
def checkStep (i : Nat) : Bool :=
  match Sym.init.run lim (ammStep i) with
  | some σ => (List.range 16).all (fun r => decide (σ.reg r = expReg i r)) && decide (σ.rax = .ld .r9 (D + 32 * i))
  | none => false

theorem checkStep_ok : ∀ i < 5, checkStep i = true := by decide +kernel

theorem run_ammStep {i : Nat} (hi : i < 5) :
    ∃ σ, Sym.init.run lim (ammStep i) = some σ ∧ ∀ r < 16, σ.reg r = expReg i r := by
  have h := checkStep_ok i hi
  unfold checkStep at h
  split at h
  · rename_i σ hσ
    refine ⟨σ, hσ, fun r hr => ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h.1 r hr
  · cases h

end VG.Proof.Bignum.X86_64.AmmSym
