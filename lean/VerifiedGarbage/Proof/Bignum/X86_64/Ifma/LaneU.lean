module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Terms
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.Amm52N

/-! ### `Bignum.X86_64.Ifma.TermsU`, which only this module used -/

section

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
noncomputable def checkStepU (p i : Nat) : Bool :=
  match ESym.init.run (limU l) (ammStepU l p i) with
  | some σ => (List.range 32).all (fun r => T.beqK (σ.reg r) (expRegU l p i r)) &&
      (if l.S ≤ i + 1 then G.beq σ.rax (.gpr .rax) else G.beq σ.rax (.ld .r9 (l.D * p + l.off (i + 1))))
  | none => false

theorem checkStepU_2048 : ∀ p < lay2048.nl, ∀ i < lay2048.S, checkStepU lay2048 p i = true := by
  decide +kernel

theorem checkStepU_p2048 : ∀ p < VG.Impl.Rsa.X86_64.PubIfma.pay2048.nl,
    ∀ i < VG.Impl.Rsa.X86_64.PubIfma.pay2048.S, checkStepU VG.Impl.Rsa.X86_64.PubIfma.pay2048 p i = true := by
  decide +kernel

theorem checkStepU_p1024 : ∀ p < VG.Impl.Rsa.X86_64.PubIfma.pay1024.nl,
    ∀ i < VG.Impl.Rsa.X86_64.PubIfma.pay1024.S, checkStepU VG.Impl.Rsa.X86_64.PubIfma.pay1024 p i = true := by
  decide +kernel

theorem checkStepU_p1536 : ∀ p < VG.Impl.Rsa.X86_64.PubIfma.pay1536.nl,
    ∀ i < VG.Impl.Rsa.X86_64.PubIfma.pay1536.S, checkStepU VG.Impl.Rsa.X86_64.PubIfma.pay1536 p i = true := by
  decide +kernel

open VG.Impl.Rsa.X86_64.PubIfma (pay1024 pay1536 pay2048) in
/-- The layouts whose multiplication has the look-ahead (`ammMul`): 2048
bits, the CRT's and the public operation's, and the one-lane 1024- and
1536-bit layouts. -/
def UOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop := l = lay2048 ∨ l = pay2048 ∨ l = pay1024 ∨ l = pay1536

variable {l} in
/-- `ammMul`'s choice: the look-ahead where the roles take at most 10 registers. -/
theorem UOk.of_amm (hl : AmmOk l) (h : l.nl * l.R ≤ 10) : UOk l := by
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact .inr (.inl rfl)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

variable {l} in
/-- The sizes the proofs of the look-ahead use: two roles or more, the
registers of the roles, the lanes' eight and the zero register. -/
theorem UOk.regs (hu : UOk l) :
    AmmOk l ∧ 2 ≤ l.R ∧ l.R ≤ 20 ∧ 1 ≤ l.nl ∧ l.nl * l.R + 8 * l.nl < 32 := by
  rcases hu with rfl | rfl | rfl | rfl
  · exact ⟨.inl (.inl rfl), by decide⟩
  · exact ⟨.inr (.inl rfl), by decide⟩
  · exact ⟨.inr (.inr (.inr (.inr (.inl rfl)))), by decide⟩
  · exact ⟨.inr (.inr (.inr (.inr (.inr rfl)))), by decide⟩

variable {l} in
theorem UOk.checkStep (hu : UOk l) : ∀ p < l.nl, ∀ i < l.S, checkStepU l p i = true := by
  rcases hu with rfl | rfl | rfl | rfl
  · exact checkStepU_2048
  · exact checkStepU_p2048
  · exact checkStepU_p1024
  · exact checkStepU_p1536

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
      exact T.eq_of_beqK (h.1 r hr)
    · simp only [Bool.and_eq_true] at h
      split at h <;> rename_i hl <;> simp only [hl, ite_true, ite_false] <;> exact G.eq_of_beq h.2
  · cases h

end VG.Proof.Bignum.X86_64.Ifma

end

end


/-!
# RSA with AVX512_IFMA on x86-64: a lane's step with the look-ahead

Under `StepInU` (the lanes of lane `p`'s roles hold the limbs `L`, below
`2⁶³`, role 0 with the low halves of `a₀ b` added; the registers of the
step's parity hold `b` and its `u`; the operands' limbs, `k₀`, and the next
limb `bn` of the second operand in memory, below `2⁵²`; the zero register
zero), the terms of `expRegU` hold the limbs of `Amm52N.step` (with the next
`lo(a₀ bn)` in the new role 0, unless the step is the last), and the next
`b` and `u`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (lo_comm mad_lo mad_hi shr_ofNat add_ofNat G.eval)
open VG.Proof.X25519.X86_64.Ifma (mad52)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- Lane `p`'s machine before its step `i`, for limbs `L`, operand limbs `a`,
modulus limbs `m`, `k₀` `k`, second-operand limb `b` and the next one `bn`. -/
structure StepInU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (p i : Nat) (L a m : Nat → Nat)
    (k b bn : Nat) : Prop where
  z : ∀ t < 4, qv s (vreg (uzN l)) t = 0
  lanes : ∀ kk < l.R, ∀ t < 4, qv s (vreg (regOf l p kk i)) t =
    BitVec.ofNat 64 (L (kk + l.R * t) + if kk = 0 then lo (a (kk + l.R * t)) b else 0)
  bv : ∀ t < 4, qv s (vreg (ubN l p (i % 2))) t = BitVec.ofNat 64 b
  uv : ∀ t < 4, qv s (vreg (uuN l p (i % 2))) t = BitVec.ofNat 64 (stepU ⟨a, m, k⟩ L b)
  lt : ∀ j < l.L, L j < 2 ^ 63
  ina : ∀ kk < l.R, ∀ t < 4,
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * kk + 8 * t)) 64 = BitVec.ofNat 64 (a (kk + l.R * t))
  inm : ∀ kk < l.R, ∀ t < 4,
    s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (l.D * p + oM + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (m (kk + l.R * t))
  ink : ∀ t < 4, s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (l.D * p + l.oK0 + 8 * t)) 64 = BitVec.ofNat 64 k
  inbn : ¬ l.S ≤ i + 1 → s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.D * p + l.off (i + 1))) 64 = BitVec.ofNat 64 bn
  alt : ∀ j < l.L, a j < 2 ^ 52
  mlt : ∀ j < l.L, m j < 2 ^ 52
  klt : k < 2 ^ 52
  blt : b < 2 ^ 52
  bnlt : bn < 2 ^ 52

section
variable {s : State} {p i : Nat} {L a m : Nat → Nat} {k b bn : Nat}

theorem idxU_lt {kk t : Nat} (hk : kk < l.R) (ht : t < 4) : kk + l.R * t < l.L := by
  have := Nat.mul_le_mul_left l.R (Nat.le_of_lt_succ ht)
  simp only [Lay.L]; omega_arith

theorem bU_eval (h : StepInU l s p i L a m k b bn) {t : Nat} (ht : t < 4) : (bU l p i).eval s t = BitVec.ofNat 64 b :=
  h.bv t ht

theorem uU_eval (h : StepInU l s p i L a m k b bn) {t : Nat} (ht : t < 4) :
    (uU l p i).eval s t = BitVec.ofNat 64 (stepU ⟨a, m, k⟩ L b) :=
  h.uv t ht

theorem a0U_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) {t : Nat} (ht : t < 4) :
    (a0U l p i).eval s t = BitVec.ofNat 64 (low ⟨a, m, k⟩ L b (0 + l.R * t)) := by
  have hl := h.lt (0 + l.R * t) (idxU_lt (by omega_arith) ht)
  have := lo_lt (a (0 + l.R * t)) b
  simp only [a0U, ldM, T.eval]
  rw [h.lanes 0 (by omega_arith) t ht, uU_eval h ht, h.inm 0 (by omega_arith) t ht, mad_lo (by split <;> omega_arith)]
  simp only [ite_true, low]

theorem m1U_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) {t : Nat} (ht : t < 4) :
    (m1U l p i).eval s t = BitVec.ofNat 64 (lo (m (1 + l.R * t)) (stepU ⟨a, m, k⟩ L b)) := by
  simp only [m1U, ldM, T.eval]
  rw [uU_eval h ht, h.inm 1 (by omega_arith) t ht, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
    mad_lo (by decide), Nat.zero_add]

theorem m2U_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) {t : Nat} (ht : t < 4) :
    (m2U l p i).eval s t = BitVec.ofNat 64 (hi (m (0 + l.R * t)) (stepU ⟨a, m, k⟩ L b)) := by
  simp only [m2U, ldM, T.eval]
  rw [uU_eval h ht, h.inm 0 (by omega_arith) t ht, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
    mad_hi (by decide), Nat.zero_add]

theorem r1aU_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) {t : Nat} (ht : t < 4) :
    (r1aU l p i).eval s t =
      BitVec.ofNat 64 (L (1 + l.R * t) + lo (a (1 + l.R * t)) b + hi (a (0 + l.R * t)) b) := by
  have hl := h.lt (1 + l.R * t) (idxU_lt hR ht)
  have := lo_lt (a (1 + l.R * t)) b
  simp only [r1aU, ldA, T.eval]
  rw [h.lanes 1 hR t ht, bU_eval h ht, h.ina 1 hR t ht, mad_lo (by split <;> omega_arith),
    h.ina 0 (by omega_arith) t ht, mad_hi (by split <;> omega_arith)]
  simp only [Nat.one_ne_zero, ite_false, Nat.add_zero]

theorem pnU_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) (hn : ¬ l.S ≤ i + 1) {t : Nat} (ht : t < 4) :
    (pnU l p i).eval s t = BitVec.ofNat 64 (lo (a (0 + l.R * t)) bn) := by
  simp only [pnU, bnU, ldA, T.eval, ite_true, G.eval]
  rw [h.inbn hn, h.ina 0 (by omega_arith) t ht, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
    mad_lo (by decide), Nat.zero_add]

theorem lowU_lt (h : StepInU l s p i L a m k b bn) {j : Nat} (hj : j < l.L) :
    low ⟨a, m, k⟩ L b j < 2 ^ 63 + 2 ^ 53 := by
  have := h.lt j hj
  have := lo_lt (a j) b
  have := lo_lt (m j) (stepU ⟨a, m, k⟩ L b)
  show L j + lo (a j) b + lo (m j) (stepU ⟨a, m, k⟩ L b) < _
  omega_arith

theorem cU_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) {t : Nat} (ht : t < 4) :
    (cU l p i).eval s t =
      BitVec.ofNat 64 (if t = 0 then low ⟨a, m, k⟩ L b 0 / 2 ^ 52 else 0) := by
  have h0 := lowU_lt h (j := 0) (by simp only [Lay.L]; omega_arith)
  simp only [cU, T.eval]
  by_cases t0 : t = 0
  · subst t0
    simp only [ite_true]
    rw [a0U_eval h hR (by decide), show (0 : Nat) + l.R * 0 = 0 by omega_arith, shr_ofNat (by omega_arith)]
  · simp only [t0, ite_false]; rfl

theorem r1U_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) {t : Nat} (ht : t < 4) :
    (r1U l p i).eval s t = BitVec.ofNat 64 (Amm52N.step l.L ⟨a, m, k⟩ L b (0 + l.R * t) +
      if l.S ≤ i + 1 then 0 else lo (a (0 + l.R * t)) bn) := by
  have hl := h.lt (1 + l.R * t) (idxU_lt hR ht)
  have h0 := lowU_lt h (j := 0) (by simp only [Lay.L]; omega_arith)
  have hc : low ⟨a, m, k⟩ L b 0 / 2 ^ 52 < 2 ^ 12 := Nat.div_lt_of_lt_mul (by omega_arith)
  have := lo_lt (a (1 + l.R * t)) b
  have := hi_lt (a (0 + l.R * t)) b
  have := lo_lt (a (0 + l.R * t)) bn
  have := lo_lt (m (1 + l.R * t)) (stepU ⟨a, m, k⟩ L b)
  have := hi_lt (m (0 + l.R * t)) (stepU ⟨a, m, k⟩ L b)
  have hRt := Nat.mul_le_mul_left l.R (Nat.le_of_lt_succ ht)
  have e1 : (r1bU l p i).eval s t = BitVec.ofNat 64 (L (1 + l.R * t) + lo (a (1 + l.R * t)) b +
      hi (a (0 + l.R * t)) b + if l.S ≤ i + 1 then 0 else lo (a (0 + l.R * t)) bn) := by
    unfold r1bU
    by_cases hn : l.S ≤ i + 1
    · simp only [hn, ite_true, Nat.add_zero]; exact r1aU_eval h hR ht
    · simp only [hn, ite_false, T.eval]
      rw [r1aU_eval h hR ht, pnU_eval h hR hn ht, add_ofNat (by omega_arith)]
  have hst : Amm52N.step l.L ⟨a, m, k⟩ L b (0 + l.R * t) =
      L (1 + l.R * t) + lo (a (1 + l.R * t)) b + lo (m (1 + l.R * t)) (stepU ⟨a, m, k⟩ L b) +
        (if t = 0 then low ⟨a, m, k⟩ L b 0 / 2 ^ 52 else 0) + hi (a (0 + l.R * t)) b +
        hi (m (0 + l.R * t)) (stepU ⟨a, m, k⟩ L b) := by
    unfold Amm52N.step Amm52N.shifted
    rw [ite_eq_left (by simp only [Lay.L]; omega_arith), show 0 + l.R * t + 1 = 1 + l.R * t by omega_arith]
    have e0 : (0 + l.R * t = 0) ↔ t = 0 := ⟨fun h0 => by
      rcases Nat.eq_zero_or_pos t with h1 | h1
      · exact h1
      · have := Nat.mul_le_mul_left l.R h1; omega_arith, fun h0 => by subst h0; omega_arith⟩
    simp only [e0, low]
  simp only [r1U, T.eval]
  rw [e1, m1U_eval h hR ht, add_ofNat (by split <;> omega_arith), m2U_eval h hR ht, add_ofNat (by split <;> omega_arith),
    cU_eval h hR ht, add_ofNat (by split <;> split <;> omega_arith), hst]
  refine congrArg (BitVec.ofNat 64) ?_
  split <;> split <;> omega_arith

theorem kU_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) (hn : ¬ l.S ≤ i + 1) :
    (kU l p i).eval s 0 = BitVec.ofNat 64 (stepU ⟨a, m, k⟩ (Amm52N.step l.L ⟨a, m, k⟩ L b) bn) := by
  simp only [kU, T.eval]
  rw [r1U_eval h hR (by decide), h.ink 0 (by decide),
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_lo (by decide), Nat.zero_add, lo_comm]
  simp only [hn, ite_false, Nat.mul_zero, Nat.add_zero, stepU]

theorem restU_eval (h : StepInU l s p i L a m k b bn) {kk t : Nat} (h2 : 2 ≤ kk) (hk : kk < l.R) (ht : t < 4) :
    (restU l p kk i).eval s t = BitVec.ofNat 64 (Amm52N.step l.L ⟨a, m, k⟩ L b (kk - 1 + l.R * t)) := by
  have hl := h.lt (kk + l.R * t) (idxU_lt hk ht)
  have := lo_lt (a (kk + l.R * t)) b
  have := hi_lt (a (kk - 1 + l.R * t)) b
  have := lo_lt (m (kk + l.R * t)) (stepU ⟨a, m, k⟩ L b)
  have := hi_lt (m (kk - 1 + l.R * t)) (stepU ⟨a, m, k⟩ L b)
  have hRt := Nat.mul_le_mul_left l.R (Nat.le_of_lt_succ ht)
  simp only [restU, ldA, ldM, T.eval]
  rw [h.lanes kk hk t ht, bU_eval h ht, h.ina kk hk t ht, mad_lo (by split <;> omega_arith),
    h.ina (kk - 1) (by omega_arith) t ht, mad_hi (by split <;> omega_arith), uU_eval h ht, h.inm kk hk t ht,
    mad_lo (by split <;> omega_arith), h.inm (kk - 1) (by omega_arith) t ht, mad_hi (by split <;> omega_arith)]
  have hst : Amm52N.step l.L ⟨a, m, k⟩ L b (kk - 1 + l.R * t) =
      low ⟨a, m, k⟩ L b (kk + l.R * t) + hi (a (kk - 1 + l.R * t)) b +
        hi (m (kk - 1 + l.R * t)) (stepU ⟨a, m, k⟩ L b) := by
    unfold Amm52N.step Amm52N.shifted
    rw [ite_eq_left (by simp only [Lay.L]; omega_arith), ite_eq_right (by omega_arith), show kk - 1 + l.R * t + 1 = kk + l.R * t by omega_arith,
      Nat.add_zero]
  rw [hst]
  refine congrArg (BitVec.ofNat 64) ?_
  simp only [show kk ≠ 0 by omega_arith, ite_false, Nat.add_zero, low]
  omega_arith

theorem topU_eval (h : StepInU l s p i L a m k b bn) (hR : 2 ≤ l.R) {t : Nat} (ht : t < 4) :
    (topU l p i).eval s t = BitVec.ofNat 64 (Amm52N.step l.L ⟨a, m, k⟩ L b (l.R - 1 + l.R * t)) := by
  have hRt := Nat.mul_le_mul_left l.R (Nat.le_of_lt_succ ht)
  have := hi_lt (a (l.R - 1 + l.R * t)) b
  have := hi_lt (m (l.R - 1 + l.R * t)) (stepU ⟨a, m, k⟩ L b)
  have hs : (if t + 1 < 4 then T.eval s (a0U l p i) (t + 1) else qv s (vreg (uzN l)) (t + 1 - 4)) =
      BitVec.ofNat 64 (Amm52N.shifted l.L (low ⟨a, m, k⟩ L b) (l.R - 1 + l.R * t)) := by
    by_cases t3 : t + 1 < 4
    · simp only [t3, ite_true]
      rw [a0U_eval h hR t3]
      have := Nat.mul_le_mul_left l.R (show t ≤ 2 by omega_arith)
      simp only [Amm52N.shifted, Lay.L, show l.R - 1 + l.R * t + 1 < 4 * l.R by omega_arith,
        show l.R - 1 + l.R * t ≠ 0 by omega_arith, ite_false, Nat.add_zero, ite_true]
      exact congrArg _ (congrArg _ (by rw [Nat.mul_add, Nat.mul_one]; omega_arith))
    · simp only [t3, ite_false]
      rw [show t + 1 - 4 = 0 by omega_arith, h.z 0 (by decide)]
      obtain rfl : t = 3 := by omega_arith
      simp only [Amm52N.shifted, Lay.L, show ¬ (l.R - 1 + l.R * 3 + 1 < 4 * l.R) by omega_arith, ite_false]
      rfl
  have hb : Amm52N.shifted l.L (low ⟨a, m, k⟩ L b) (l.R - 1 + l.R * t) < 2 ^ 63 + 2 ^ 54 := by
    unfold Amm52N.shifted
    split
    · have := lowU_lt h (j := l.R - 1 + l.R * t + 1) (by omega_arith)
      simp only [show l.R - 1 + l.R * t ≠ 0 by omega_arith, ite_false]; omega_arith
    · omega_arith
  simp only [topU, ldA, ldM, T.eval]
  rw [hs, bU_eval h ht, h.ina (l.R - 1) (by omega_arith) t ht, mad_hi (by omega_arith), uU_eval h ht,
    h.inm (l.R - 1) (by omega_arith) t ht, mad_hi (by omega_arith)]
  rfl

end

end VG.Proof.Bignum.X86_64.Ifma
