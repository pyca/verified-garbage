module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.LaneU
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64: the steps with the look-ahead, 2048 bits

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

theorem R2048 : lay2048.R = 5 := rfl
theorem S2048 : lay2048.S = 20 := rfl
theorem nl2048 : lay2048.nl = 2 := rfl


def b0U (p : Nat) : T := .bc (.lane0 (.ld .r9 (lay2048.D * p)))
def s0U (p : Nat) : T := .mad false (.reg (regOf lay2048 p 0 0)) (b0U p) (ldA lay2048 p 0)
def k0U (p : Nat) : T := .mad false .zero (s0U p) (.ld .r10 (lay2048.D * p + lay2048.oK0))

def expStartU (p r : Nat) : T :=
  if r = regOf lay2048 p 0 0 then s0U p
  else if r = ubN lay2048 p 0 then b0U p
  else if r = utN lay2048 p then k0U p
  else if r = uuN lay2048 p 0 then .bc (k0U p)
  else .reg r

def checkStartU (p : Nat) : Bool :=
  match ESym.init.run (limU lay2048) (ammStartU lay2048 p) with
  | some σ => (List.range 32).all (fun r => T.beq (σ.reg r) (expStartU p r))
  | none => false

theorem checkStartU_2048 : ∀ p < lay2048.nl, checkStartU p = true := by decide +kernel

theorem run_ammStartU {p : Nat} (hp : p < lay2048.nl) :
    ∃ σ, ESym.init.run (limU lay2048) (ammStartU lay2048 p) = some σ ∧ ∀ r < 32, σ.reg r = expStartU p r := by
  have h := checkStartU_2048 p hp
  unfold checkStartU at h
  split at h
  · rename_i σ hσ
    refine ⟨σ, hσ, fun r hr => ?_⟩
    simp only [List.all_eq_true, List.mem_range] at h
    exact T.eq_of_beq (h r hr)
  · cases h

theorem regsS2048 (p : Nat) :
    regOf lay2048 p 0 0 = 5 * p + (0 + 0) % 5 ∧ ubN lay2048 p 0 = 10 + 8 * p + 0 ∧
      uuN lay2048 p 0 = 10 + 8 * p + 2 + 0 ∧ utN lay2048 p = 10 + 8 * p + 4 :=
  ⟨by simp only [regOf, show lay2048.R = 5 from rfl], rfl, rfl, rfl⟩

/-- Lane `p`'s start: `b₀` (`b`), role 0 plus `lo(a₀ b₀)`, and `u₀`. -/
theorem ammStartU_ok {s : State} {p : Nat} (hp : p < 2) {a m : Nat → Nat} {k b : Nat}
    (hc : Ctx (limU lay2048) s) (h0 : ∀ t < 4, qv s (vreg (regOf lay2048 p 0 0)) t = 0)
    (ina : ∀ t < 4, s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (lay2048.D * p + 32 * 0 + 8 * t)) 64 =
      BitVec.ofNat 64 (a (0 + lay2048.R * t)))
    (ink : s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (lay2048.D * p + lay2048.oK0 + 8 * 0)) 64 = BitVec.ofNat 64 k)
    (inb : s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (lay2048.D * p)) 64 = BitVec.ofNat 64 b) :
    WP isa (.block (ammStartU lay2048 p)) s fun s' =>
      (∀ t < 4, qv s' (vreg (regOf lay2048 p 0 0)) t = BitVec.ofNat 64 (0 + lo (a (0 + lay2048.R * t)) b)) ∧
      (∀ t < 4, qv s' (vreg (ubN lay2048 p 0)) t = BitVec.ofNat 64 b) ∧
      (∀ t < 4, qv s' (vreg (uuN lay2048 p 0)) t = BitVec.ofNat 64 (stepU ⟨a, m, k⟩ (fun _ => 0) b)) ∧
      (∀ r < 32, r ≠ regOf lay2048 p 0 0 → r ≠ ubN lay2048 p 0 → r ≠ utN lay2048 p → r ≠ uuN lay2048 p 0 →
        ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) ∧
      Keeps s s' := by
  obtain ⟨σ, e, hσ⟩ := run_ammStartU (p := p) (by rw [nl2048]; exact hp)
  have := regsS2048 p
  have hs0 : ∀ t < 4, (s0U p).eval s t = BitVec.ofNat 64 (0 + lo (a (0 + lay2048.R * t)) b) := fun t ht => by
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


theorem regOf2048 {p kk j : Nat} :
    5 * p ≤ regOf lay2048 p kk j ∧ regOf lay2048 p kk j < 5 * p + 5 := by
  have := Nat.mod_lt (kk + j) (show 0 < 5 by decide)
  simp only [regOf, R2048]; omega

/-- Role `kk` at step `i + 1` was role `kk + 1` at step `i`. -/
theorem roleAt_regOf {l : Lay} (hR : 0 < l.R) {p kk i : Nat} :
    roleAt l (regOf l p kk (i + 1)) i = (kk + 1) % l.R := by
  unfold roleAt
  rw [regOf_mod, show kk + (i + 1) = kk + 1 + i by omega, Nat.add_mod (kk + 1)]
  exact mod_role (Nat.mod_lt _ hR) (Nat.mod_lt _ hR)

theorem expRegU_role {p i kk : Nat} (hk : kk < 5) :
    expRegU lay2048 p i (regOf lay2048 p kk (i + 1)) =
      if kk = 4 then topU lay2048 p i else if kk = 0 then r1U lay2048 p i else restU lay2048 p (kk + 1) i := by
  have hr := regOf2048 (p := p) (kk := kk) (j := i + 1)
  have hro := roleAt_regOf (l := lay2048) (by decide) (p := p) (kk := kk) (i := i)
  rw [R2048] at hro
  unfold expRegU
  rw [ite_eq_left (by rw [R2048]; omega), hro]
  rcases (by omega : kk = 0 ∨ kk = 1 ∨ kk = 2 ∨ kk = 3 ∨ kk = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem regsU2048 (p i : Nat) :
    lay2048.R * p = 5 * p ∧ lay2048.R = 5 ∧ ubN lay2048 p ((i + 1) % 2) = 10 + 8 * p + (i + 1) % 2 ∧
      uuN lay2048 p ((i + 1) % 2) = 10 + 8 * p + 2 + (i + 1) % 2 ∧ utN lay2048 p = 10 + 8 * p + 4 ∧
      um1N lay2048 p = 10 + 8 * p + 5 ∧ um2N lay2048 p = 10 + 8 * p + 6 ∧ upnN lay2048 p = 10 + 8 * p + 7 ∧
      (i + 1) % 2 < 2 :=
  ⟨by rw [R2048], rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.mod_lt _ (by decide)⟩

theorem expRegU_other {p i r : Nat} (h1 : r < 5 * p ∨ 5 * p + 5 ≤ r) (h2 : r < 10 + 8 * p ∨ 18 + 8 * p ≤ r) :
    expRegU lay2048 p i r = .reg r := by
  have := regsU2048 p i
  simp (disch := omega) only [expRegU, ↓ite_eq_right]

theorem expRegU_ub {p i : Nat} (hn : ¬ lay2048.S ≤ i + 1) :
    expRegU lay2048 p i (ubN lay2048 p ((i + 1) % 2)) = bnU lay2048 p i := by
  have := regsU2048 p i
  simp (disch := omega) only [expRegU, ↓ite_eq_right, ↓ite_eq_left]

theorem expRegU_uu {p i : Nat} (hn : ¬ lay2048.S ≤ i + 1) :
    expRegU lay2048 p i (uuN lay2048 p ((i + 1) % 2)) = .bc (kU lay2048 p i) := by
  have := regsU2048 p i
  simp (disch := omega) only [expRegU, ↓ite_eq_right, ↓ite_eq_left]

/-- Lane `p`'s step `i`. -/
theorem ammStepU_ok {s : State} {p i : Nat} (hp : p < 2) (hi : i < 20) {L a m : Nat → Nat} {k b bn : Nat}
    (h : StepInU lay2048 s p i L a m k b bn) (hc : Ctx (limU lay2048) s) :
    WP isa (.block (ammStepU lay2048 p i)) s fun s' =>
      (∀ kk < lay2048.R, ∀ t < 4, qv s' (vreg (regOf lay2048 p kk (i + 1))) t =
        BitVec.ofNat 64 (Amm52N.step lay2048.L ⟨a, m, k⟩ L b (kk + lay2048.R * t) +
          if kk = 0 ∧ ¬ lay2048.S ≤ i + 1 then lo (a (kk + lay2048.R * t)) bn else 0)) ∧
      (¬ lay2048.S ≤ i + 1 → ∀ t < 4, qv s' (vreg (ubN lay2048 p ((i + 1) % 2))) t = BitVec.ofNat 64 bn) ∧
      (¬ lay2048.S ≤ i + 1 → ∀ t < 4, qv s' (vreg (uuN lay2048 p ((i + 1) % 2))) t =
        BitVec.ofNat 64 (stepU ⟨a, m, k⟩ (Amm52N.step lay2048.L ⟨a, m, k⟩ L b) bn)) ∧
      (∀ r < 32, (r < 5 * p ∨ 5 * p + 5 ≤ r) → (r < 10 + 8 * p ∨ 18 + 8 * p ≤ r) →
        ∀ t < 4, qv s' (vreg r) t = qv s (vreg r) t) ∧
      Keeps s s' := by
  have hR : 2 ≤ lay2048.R := by decide
  obtain ⟨σ, e, hσ, _⟩ := run_ammStepU (p := p) (i := i) (by rw [nl2048]; exact hp) (by rw [S2048]; exact hi)
  refine WP.mono (run_ok hc (SRel.init s) e) fun s' hs => ⟨fun kk hk t ht => ?_, fun hn t ht => ?_,
    fun hn t ht => ?_, fun r hr h1 h2 t ht => ?_, ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
  · rw [R2048] at hk
    have hr := regOf2048 (p := p) (kk := kk) (j := i + 1)
    rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega), expRegU_role hk]
    rcases (by omega : kk = 0 ∨ (1 ≤ kk ∧ kk ≤ 3) ∨ kk = 4) with rfl | hk' | rfl
    · rw [ite_eq_right (by decide), ite_eq_left rfl, r1U_eval h hR ht]
      by_cases hn : lay2048.S ≤ i + 1 <;> simp only [hn, ite_true, ite_false, true_and, not_true, not_false_eq_true]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), restU_eval h (by omega) (by rw [R2048]; omega) ht,
        ite_eq_right (by omega), Nat.add_sub_cancel]
      exact congrArg _ (Nat.add_zero _).symm
    · rw [ite_eq_left rfl, topU_eval h hR ht, ite_eq_right (by omega), Nat.add_zero,
        show lay2048.R - 1 = 4 from rfl]
  · have := regsU2048 p i
    rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega), expRegU_ub hn]
    simp only [bnU, T.eval, ite_true, G.eval]
    exact h.inbn hn
  · have := regsU2048 p i
    rw [hs.reg _ t ht, vi_vreg _ (by omega), hσ _ (by omega), expRegU_uu hn]
    exact kU_eval h hR hn
  · rw [hs.reg _ t ht, vi_vreg _ hr, hσ _ hr, expRegU_other h1 h2]
    rfl

end VG.Proof.Bignum.X86_64.Ifma
