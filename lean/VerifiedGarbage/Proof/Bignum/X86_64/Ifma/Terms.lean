module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ESym
public import VerifiedGarbage.Impl.Rsa.X86_64.PubIfma
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64, any size: the terms of a step

For `CrtIfma.ammStep l i`, the terms `ESym.run` computes for
step `i` of a block, written for any `i` and `l` (`expReg`), and checked
against the run for each `i < R` of each layout (`StepsOk`).

For each lane `p` (below `nl`, at `D p` from each base): `bT` the limb of the
second operand, broadcast; `a1T` the accumulator of role `k` plus the low
halves of `a b`; `a1hT` plus, for `k ≥ 1`, the high halves of role `k - 1`
of `a b`; `uT` the factor `u`, broadcast; `a2T` plus the low halves of
`u m`; `cT` the carry of role 0's lane 0, in lane 0; `nT` role `k` after the
shift (role `k + 1`, with the carry for role 0, and role 0's lanes moved
down for role `R - 1`); `hT` plus the high halves of `u m` (and, for role
`R - 1`, of `a b`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (G)

variable (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay)

/-- The bytes each base may be loaded from: the operands and the modulus' region. -/
def lim : Reg → Nat := fun b =>
  if b = .r8 then l.D * (l.nl - 1) + l.NB else if b = .r9 then l.D * (l.nl - 1) + 32 * (l.R - 1) + 8
  else if b = .r10 then l.D * (l.nl - 1) + l.NB + 32 else 0

/-- The register number of role `k` of prime `p` at step `i`. -/
def regOf (p k i : Nat) : Nat := l.R * p + (k + i) % l.R

/-- The zero register and the temporary. -/
def zN : Nat := l.nl * l.R + 2 * l.nl
def tN : Nat := l.nl * l.R + 2 * l.nl + 1

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
  if r < l.nl * l.R then hT l (r / l.R) (roleOf l r i) i
  else if r < l.nl * l.R + l.nl then bT l (r - l.nl * l.R) i
  else if r < l.nl * l.R + 2 * l.nl then uT l (r - l.nl * l.R - l.nl) i
  else if r = tN l then cT l (l.nl - 1) i else .reg r

/-- The run of the steps gives `expReg i` in the 32 registers and loads `rax`. -/
abbrev StepsOk : Prop :=
  ((List.range l.R).map fun i => ESym.runK (lim l) (ammStep l i) (List.range 32)) =
    (List.range l.R).map fun i => some ((List.range 32).map (expReg l i), .ld .r9 (l.D * (l.nl - 1) + 32 * i))

/-- The layouts the code runs. -/
def LayOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop :=
  l = lay2048 ∨ l = lay3072 ∨ l = lay4096 ∨ l = lay2048z

/-- The two layouts for 2048-bit keys, one in each function. -/
def Lay2 (l2 : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop := l2 = lay2048 ∨ l2 = lay2048z

/-- The layouts of the function whose layout for 2048-bit keys is `l2`. -/
def LayOf (l2 l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop := l = l2 ∨ l = lay3072 ∨ l = lay4096

theorem LayOf.ok {l2 l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (hl : LayOf l2 l) (h2 : Lay2 l2) : LayOk l := by
  rcases hl with rfl | rfl | rfl
  · rcases h2 with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr (.inr rfl))
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))

theorem checkStep_2048 : StepsOk lay2048 := by delta StepsOk; kernel_rfl
theorem checkStep_3072 : StepsOk lay3072 := by delta StepsOk; kernel_rfl
theorem checkStep_4096 : StepsOk lay4096 := by delta StepsOk; kernel_rfl
theorem checkStep_2048z : StepsOk lay2048z := by delta StepsOk; kernel_rfl

open VG.Impl.Rsa.X86_64.PubIfma (pay1024 pay1536 pay2048 pay3072 pay4096) in
/-- The layouts the multiplication runs: the CRT's, the public operation's,
and the one-lane layouts of 1024- and 1536-bit Miller–Rabin candidates. -/
def AmmOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop :=
  LayOk l ∨ l = pay2048 ∨ l = pay3072 ∨ l = pay4096 ∨ l = pay1024 ∨ l = pay1536

theorem LayOk.amm {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (hl : LayOk l) : AmmOk l := .inl hl

/-- The CRT's layouts are among those of the multiplication. -/
instance {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} : Coe (LayOk l) (AmmOk l) := ⟨LayOk.amm⟩

theorem checkStep_p2048 : StepsOk VG.Impl.Rsa.X86_64.PubIfma.pay2048 := by delta StepsOk; kernel_rfl
theorem checkStep_p3072 : StepsOk VG.Impl.Rsa.X86_64.PubIfma.pay3072 := by delta StepsOk; kernel_rfl
theorem checkStep_p4096 : StepsOk VG.Impl.Rsa.X86_64.PubIfma.pay4096 := by delta StepsOk; kernel_rfl

theorem checkStep_p1024 : StepsOk VG.Impl.Rsa.X86_64.PubIfma.pay1024 := by delta StepsOk; kernel_rfl
theorem checkStep_p1536 : StepsOk VG.Impl.Rsa.X86_64.PubIfma.pay1536 := by delta StepsOk; kernel_rfl

theorem checkStep_ok {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (hl : AmmOk l) : StepsOk l := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  · exact checkStep_2048
  · exact checkStep_3072
  · exact checkStep_4096
  · exact checkStep_2048z
  · exact checkStep_p2048
  · exact checkStep_p3072
  · exact checkStep_p4096
  · exact checkStep_p1024
  · exact checkStep_p1536

theorem run_ammStep {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay} (hl : AmmOk l) {i : Nat} (hi : i < l.R) :
    ∃ σ, ESym.init.run (lim l) (ammStep l i) = some σ ∧ ∀ r < 32, σ.reg r = expReg l i r := by
  obtain ⟨σ, hσ, h, -⟩ := ESym.runK_ok (fun _ => List.mem_range.mp)
    (List.map_inj_left.mp (checkStep_ok hl) i (List.mem_range.mpr hi))
  exact ⟨σ, hσ, fun r hr => List.map_inj_left.mp h r (List.mem_range.mpr hr)⟩

end VG.Proof.Bignum.X86_64.Ifma
