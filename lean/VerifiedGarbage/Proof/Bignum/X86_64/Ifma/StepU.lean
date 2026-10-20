module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.LaneU
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64: the steps with the look-ahead

`ammStartU` loads lane `p`'s first limb `b₀` of the second operand, adds
`lo(a₀ b₀)` to role 0 and computes `u₀` (`ammStartU_ok`); from `StepInU`,
lane `p`'s step `i` leaves the limbs of `Amm52N.step` in the roles of step
`i + 1`, with the next `lo(a₀ bn)` in role 0 and `bn` and its `u` in the
registers of the next parity unless the step is the last, and changes no
other register of the other lane (`ammStepU_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (G Ctx Keeps mad_lo lo_comm)

/-! ## The start -/

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

def b0U (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) : T := .bc (.lane0 (.ld .r9 (l.D * p)))
def s0U (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) : T :=
  .mad false (.reg (regOf l p 0 0)) (b0U l p) (ldA l p 0)
def k0U (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) : T := .mad false .zero (s0U l p) (.ld .r10 (l.D * p + l.oK0))

def expStartU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p r : Nat) : T :=
  if r = regOf l p 0 0 then s0U l p
  else if r = ubN l p 0 then b0U l p
  else if r = utN l p then k0U l p
  else if r = uuN l p 0 then .bc (k0U l p)
  else .reg r

def checkStartU (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (p : Nat) : Bool :=
  match ESym.init.run (limU l) (ammStartU l p) with
  | some σ => (List.range 32).all (fun r => T.beq (σ.reg r) (expStartU l p r))
  | none => false

theorem checkStartU_2048 : ∀ p < lay2048.nl, checkStartU lay2048 p = true := by decide +kernel

theorem checkStartU_p2048 : ∀ p < VG.Impl.Rsa.X86_64.PubIfma.pay2048.nl,
    checkStartU VG.Impl.Rsa.X86_64.PubIfma.pay2048 p = true := by decide +kernel

theorem UOk.checkStart (hu : UOk l) : ∀ p < l.nl, checkStartU l p = true := by
  rcases hu with rfl | rfl
  · exact checkStartU_2048
  · exact checkStartU_p2048

theorem run_ammStartU (hu : UOk l) {p : Nat} (hp : p < l.nl) :
    ∃ σ, ESym.init.run (limU l) (ammStartU l p) = some σ ∧ ∀ r < 32, σ.reg r = expStartU l p r := by
  have h := hu.checkStart p hp
  unfold checkStartU at h
  split at h
  · rename_i σ hσ
    refine ⟨σ, hσ, fun r hr => ?_⟩
    simp only [List.all_eq_true, List.mem_range] at h
    exact T.eq_of_beq (h r hr)
  · cases h

/-- Lane `p`'s first role and the look-ahead's registers of the start. -/
theorem regsS {p : Nat} (hp : p < l.nl) :
    regOf l p 0 0 = l.R * p ∧ l.R * p + l.R ≤ l.nl * l.R ∧ ubN l p 0 = l.nl * l.R + 8 * p ∧
      uuN l p 0 = l.nl * l.R + 8 * p + 2 ∧ utN l p = l.nl * l.R + 8 * p + 4 ∧ 8 * p + 8 ≤ 8 * l.nl := by
  have := Nat.mul_le_mul_left l.R (show p + 1 ≤ l.nl by omega)
  refine ⟨by simp only [regOf, Nat.add_zero, Nat.zero_mod], by rw [Nat.mul_comm l.nl]; rw [Nat.mul_add, Nat.mul_one] at this; omega,
    rfl, rfl, rfl, by omega⟩

/-- Lane `p`'s start: `b₀` (`b`), role 0 plus `lo(a₀ b₀)`, and `u₀`. -/
theorem ammStartU_ok (hu : UOk l) {s : State} {p : Nat} (hp : p < l.nl) {a m : Nat → Nat} {k b : Nat}
    (hc : Ctx (limU l) s) (h0 : ∀ t < 4, qv s (vreg (regOf l p 0 0)) t = 0)
    (ina : ∀ t < 4, s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * 0 + 8 * t)) 64 =
      BitVec.ofNat 64 (a (0 + l.R * t)))
    (ink : s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (l.D * p + l.oK0 + 8 * 0)) 64 = BitVec.ofNat 64 k)
    (inb : s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.D * p)) 64 = BitVec.ofNat 64 b) :
    WP isa (.block (ammStartU l p)) s fun s' =>
      (∀ t < 4, qv s' (vreg (regOf l p 0 0)) t = BitVec.ofNat 64 (0 + lo (a (0 + l.R * t)) b)) ∧
      (∀ t < 4, qv s' (vreg (ubN l p 0)) t = BitVec.ofNat 64 b) ∧
      (∀ t < 4, qv s' (vreg (uuN l p 0)) t = BitVec.ofNat 64 (stepU ⟨a, m, k⟩ (fun _ => 0) b)) ∧
      (∀ r < 32, r ≠ regOf l p 0 0 → r ≠ ubN l p 0 → r ≠ utN l p → r ≠ uuN l p 0 →
        ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) ∧
      Keeps s s' := by
  obtain ⟨-, hR, -, -, hb⟩ := hu.regs
  obtain ⟨σ, e, hσ⟩ := run_ammStartU hu hp
  have := regsS hp
  have hs0 : ∀ t < 4, (s0U l p).eval s t = BitVec.ofNat 64 (0 + lo (a (0 + l.R * t)) b) := fun t ht => by
    simp only [s0U, b0U, ldA, T.eval, ite_true, G.eval]
    rw [h0 t ht, inb, ina t ht, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_lo (by decide)]
  refine WP.mono (run_ok hc (SRel.init s) e) fun s' hs => ⟨fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_, fun r hr h1 h2 h3 h4 t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
  · rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega)]
    simp only [expStartU, ite_true]
    exact hs0 t ht
  · rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega)]
    simp (disch := omega) only [expStartU, ↓ite_eq_right, ↓ite_eq_left]
    simp only [b0U, T.eval, ite_true, G.eval]
    exact inb
  · rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega)]
    simp (disch := omega) only [expStartU, ↓ite_eq_right, ↓ite_eq_left]
    simp only [k0U, T.eval]
    rw [hs0 0 (by decide), ink, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_lo (by decide),
      Nat.zero_add, lo_comm]
    rfl
  · rw [hs.reg _ t ht, vi_vreg _ hr, hσ _ hr]
    simp (disch := omega) only [expStartU, ↓ite_eq_right]
    rfl

/-! ## The registers of a step -/

theorem regOf_bounds (hR : 0 < l.R) {p kk j : Nat} :
    l.R * p ≤ regOf l p kk j ∧ regOf l p kk j < l.R * p + l.R := by
  have := Nat.mod_lt (kk + j) hR
  simp only [regOf]; omega

/-- Role `kk` at step `i + 1` was role `kk + 1` at step `i`. -/
theorem roleAt_regOf (hR : 0 < l.R) {p kk i : Nat} :
    roleAt l (regOf l p kk (i + 1)) i = (kk + 1) % l.R := by
  unfold roleAt
  rw [regOf_mod, show kk + (i + 1) = kk + 1 + i by omega, Nat.add_mod (kk + 1)]
  exact mod_role (Nat.mod_lt _ hR) (Nat.mod_lt _ hR)

theorem expRegU_role (hR : 2 ≤ l.R) {p i kk : Nat} (hk : kk < l.R) :
    expRegU l p i (regOf l p kk (i + 1)) =
      if kk = l.R - 1 then topU l p i else if kk = 0 then r1U l p i else restU l p (kk + 1) i := by
  have hr := regOf_bounds (l := l) (by omega) (p := p) (kk := kk) (j := i + 1)
  have hro := roleAt_regOf (l := l) (by omega) (p := p) (kk := kk) (i := i)
  unfold expRegU
  rw [ite_eq_left hr, hro]
  by_cases h1 : kk = l.R - 1
  · rw [ite_eq_left h1, show (kk + 1) % l.R = 0 by rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_self], ite_eq_left rfl]
  · rw [ite_eq_right h1, Nat.mod_eq_of_lt (show kk + 1 < l.R by omega)]
    by_cases h0 : kk = 0
    · subst h0; rw [ite_eq_right (by decide), ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h0]

/-- The look-ahead's registers of lane `p` after its step `i`. -/
theorem regsU {p : Nat} (hp : p < l.nl) (i : Nat) :
    l.R * p + l.R ≤ l.nl * l.R ∧ 8 * p + 8 ≤ 8 * l.nl ∧
      ubN l p ((i + 1) % 2) = l.nl * l.R + 8 * p + (i + 1) % 2 ∧
      uuN l p ((i + 1) % 2) = l.nl * l.R + 8 * p + 2 + (i + 1) % 2 ∧ utN l p = l.nl * l.R + 8 * p + 4 ∧
      um1N l p = l.nl * l.R + 8 * p + 5 ∧ um2N l p = l.nl * l.R + 8 * p + 6 ∧
      upnN l p = l.nl * l.R + 8 * p + 7 ∧ (i + 1) % 2 < 2 :=
  ⟨(regsS hp).2.1, by omega, rfl, rfl, rfl, rfl, rfl, rfl, Nat.mod_lt _ (by decide)⟩

theorem expRegU_other {p i r : Nat} (h1 : r < l.R * p ∨ l.R * p + l.R ≤ r)
    (h2 : r < l.nl * l.R + 8 * p ∨ l.nl * l.R + 8 * p + 8 ≤ r) :
    expRegU l p i r = .reg r := by
  have : ubN l p ((i + 1) % 2) = l.nl * l.R + 8 * p + (i + 1) % 2 ∧
      uuN l p ((i + 1) % 2) = l.nl * l.R + 8 * p + 2 + (i + 1) % 2 ∧ utN l p = l.nl * l.R + 8 * p + 4 ∧
      um1N l p = l.nl * l.R + 8 * p + 5 ∧ um2N l p = l.nl * l.R + 8 * p + 6 ∧
      upnN l p = l.nl * l.R + 8 * p + 7 ∧ (i + 1) % 2 < 2 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.mod_lt _ (by decide)⟩
  simp (disch := omega) only [expRegU, ↓ite_eq_right]

theorem expRegU_ub {p i : Nat} (hp : p < l.nl) (hn : ¬ l.S ≤ i + 1) :
    expRegU l p i (ubN l p ((i + 1) % 2)) = bnU l p i := by
  have := regsU hp i
  simp (disch := omega) only [expRegU, ↓ite_eq_right, ↓ite_eq_left]

theorem expRegU_uu {p i : Nat} (hp : p < l.nl) (hn : ¬ l.S ≤ i + 1) :
    expRegU l p i (uuN l p ((i + 1) % 2)) = .bc (kU l p i) := by
  have := regsU hp i
  simp (disch := omega) only [expRegU, ↓ite_eq_right, ↓ite_eq_left]

/-- Lane `p`'s step `i`. -/
theorem ammStepU_ok (hu : UOk l) {s : State} {p i : Nat} (hp : p < l.nl) (hi : i < l.S) {L a m : Nat → Nat}
    {k b bn : Nat} (h : StepInU l s p i L a m k b bn) (hc : Ctx (limU l) s) :
    WP isa (.block (ammStepU l p i)) s fun s' =>
      (∀ kk < l.R, ∀ t < 4, qv s' (vreg (regOf l p kk (i + 1))) t =
        BitVec.ofNat 64 (Amm52N.step l.L ⟨a, m, k⟩ L b (kk + l.R * t) +
          if kk = 0 ∧ ¬ l.S ≤ i + 1 then lo (a (kk + l.R * t)) bn else 0)) ∧
      (¬ l.S ≤ i + 1 → ∀ t < 4, qv s' (vreg (ubN l p ((i + 1) % 2))) t = BitVec.ofNat 64 bn) ∧
      (¬ l.S ≤ i + 1 → ∀ t < 4, qv s' (vreg (uuN l p ((i + 1) % 2))) t =
        BitVec.ofNat 64 (stepU ⟨a, m, k⟩ (Amm52N.step l.L ⟨a, m, k⟩ L b) bn)) ∧
      (∀ r < 32, (r < l.R * p ∨ l.R * p + l.R ≤ r) → (r < l.nl * l.R + 8 * p ∨ l.nl * l.R + 8 * p + 8 ≤ r) →
        ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) ∧
      Keeps s s' := by
  obtain ⟨-, hR, -, -, hb⟩ := hu.regs
  have hg := regsU hp i
  obtain ⟨σ, e, hσ, _⟩ := run_ammStepU hu hp hi
  refine WP.mono (run_ok hc (SRel.init s) e) fun s' hs => ⟨fun kk hk t ht => ?_, fun hn t ht => ?_,
    fun hn t ht => ?_, fun r hr h1 h2 t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
  · have hr := regOf_bounds (l := l) (by omega) (p := p) (kk := kk) (j := i + 1)
    rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega), expRegU_role hR hk]
    rcases (by omega : kk = 0 ∨ (1 ≤ kk ∧ kk + 2 ≤ l.R) ∨ kk = l.R - 1) with rfl | hk' | rfl
    · rw [ite_eq_right (by omega), ite_eq_left rfl, r1U_eval h hR ht]
      by_cases hn : l.S ≤ i + 1 <;> simp only [hn, ite_true, ite_false, true_and, not_true, not_false_eq_true]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), restU_eval h (by omega) (by omega) ht,
        ite_eq_right (by omega), Nat.add_sub_cancel]
      exact congrArg _ (Nat.add_zero _).symm
    · rw [ite_eq_left rfl, topU_eval h hR ht, ite_eq_right (by omega), Nat.add_zero]
  · rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega), expRegU_ub hp hn]
    simp only [bnU, T.eval, ite_true, G.eval]
    exact h.inbn hn
  · rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega), expRegU_uu hp hn]
    exact kU_eval h hR hn
  · rw [hs.reg _ t ht, vi_vreg _ hr, hσ _ hr, expRegU_other h1 h2]
    rfl

end VG.Proof.Bignum.X86_64.Ifma
