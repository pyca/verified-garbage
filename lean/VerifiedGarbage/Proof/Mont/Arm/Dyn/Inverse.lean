module

public import VerifiedGarbage.Impl.Mont.Arm.Context
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: `m'`

`setupInverse mo` stores `-m⁻¹ mod 2¹⁶` at `[invO]` for the odd modulus at
`[mo]` (`setupInverse_ok`): from `x = m mod 2¹⁶`, an inverse modulo 8, three
Newton steps (`newton_ok`) give one modulo `2²⁴`.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_mul wp_movw op2_imm op2_reg dpVal)
open VG.Proof.Bignum (hensel_step_int odd_sq emod_pow_weaken)

/-- Hensel lifting with a 32-bit result. -/
theorem newton_step {a x x' : Int} {j : Nat} (hj : 2 * j ≤ 32) (h : (a * x - 1) % (2 ^ j : Int) = 0)
    (hx : (x' - x * (2 - a * x)) % (2 ^ 32 : Int) = 0) : (a * x' - 1) % (2 ^ (2 * j) : Int) = 0 := by
  have h1 := Int.dvd_of_emod_eq_zero (hensel_step_int a x j h)
  have h2 : (2 ^ (2 * j) : Int) ∣ x' - x * (2 - a * x) :=
    Int.dvd_trans (show (2 ^ (2 * j) : Int) ∣ 2 ^ 32 from
      ⟨2 ^ (32 - 2 * j), by rw [← Int.pow_add, Nat.add_sub_cancel' hj]⟩) (Int.dvd_of_emod_eq_zero hx)
  apply Int.emod_eq_zero_of_dvd
  have : a * x' - 1 = a * (x' - x * (2 - a * x)) + (a * (x * (2 - a * x)) - 1) := by grind
  rw [this]
  exact Int.dvd_add (Int.dvd_trans h2 (Int.dvd_mul_left a _)) h1

theorem ofNat_mod32 (n : Nat) : ((BitVec.ofNat 32 n).toNat : Int) % 2 ^ 32 = (n : Int) % 2 ^ 32 := by
  rw [BitVec.toNat_ofNat, Int.natCast_emod]
  exact Int.emod_emod _ _

/-- The machine's Newton step, as integers modulo `2³²`. -/
theorem newton_val (a x : BitVec 32) :
    ((x * ((0x2 : BitVec 16).setWidth 32 - a * x)).toNat : Int) % 2 ^ 32 =
      ((x.toNat : Int) * (2 - (a.toNat : Int) * x.toNat)) % 2 ^ 32 := by
  have sub_mod (y : BitVec 32) : (((0x2 : BitVec 16).setWidth 32 - y).toNat : Int) % 2 ^ 32 =
      (2 - (y.toNat : Int)) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, show ((0x2 : BitVec 16).setWidth 32).toNat = 2 from rfl,
      Int.natCast_emod, show ((2 ^ 32 : Nat) : Int) = 2 ^ 32 from rfl, Int.emod_emod]
    have hy := y.isLt
    omega
  rw [BitVec.toNat_mul, Int.natCast_emod, show ((2 ^ 32 : Nat) : Int) = 2 ^ 32 from rfl, Int.emod_emod,
    Int.natCast_mul, Int.mul_emod, sub_mod, Int.sub_emod, BitVec.toNat_mul, Int.natCast_emod,
    show ((2 ^ 32 : Nat) : Int) = 2 ^ 32 from rfl, Int.emod_emod, Int.natCast_mul, ← Int.sub_emod, ← Int.mul_emod]

/-- `r7 := r7 (2 - r5 r7)`. -/
theorem newton_ok (s : State) :
    WP isa (.block newton) s fun t =>
      (((t.gpr .r7).toNat : Int) - (s.gpr .r7).toNat * (2 - (s.gpr .r5).toNat * (s.gpr .r7).toNat)) %
        (2 ^ 32 : Int) = 0 ∧ Rest [.r2, .r4, .r7] s t ∧ t.mem = s.mem := by
  unfold newton
  refine wp_mul fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => wp_mul fun s₄ u₄ =>
    WP.block_nil ⟨?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · simp only [u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (newton_val _ _)
  · exact ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans ((u₃.rest (by decide)).trans (u₄.rest (by decide)))

theorem newton_step_ok (s : State) {j : Nat} (hj : 2 * j ≤ 32)
    (h : (((s.gpr .r5).toNat : Int) * (s.gpr .r7).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) s fun t =>
      (((t.gpr .r5).toNat : Int) * (t.gpr .r7).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
      Rest [.r2, .r4, .r7] s t ∧ t.mem = s.mem :=
  WP.mono (newton_ok s) fun t ⟨hv, k, hm⟩ => ⟨by rw [k.gpr .r5 (by decide)]; exact newton_step hj h hv, k, hm⟩

/-- `-x mod 2¹⁶` is `-a⁻¹` for an inverse `x` of `a` modulo `2¹⁶`. -/
theorem neg_inv16 {a x : Nat} (hx : x < 2 ^ 32) (h : ((a : Int) * x - 1) % (2 ^ 16 : Int) = 0) :
    (a * ((2 ^ 32 - x) % 2 ^ 32 % 2 ^ 16) + 1) % 2 ^ 16 = 0 := by
  have hr : (((2 ^ 32 - x) % 2 ^ 32 % 2 ^ 16 : Nat) : Int) % 2 ^ 16 = -(x : Int) % 2 ^ 16 := by omega
  have h2 : ((a * ((2 ^ 32 - x) % 2 ^ 32 % 2 ^ 16) + 1 : Nat) : Int) % 2 ^ 16 =
      (-((a : Int) * x - 1)) % 2 ^ 16 := by
    rw [Int.natCast_add, Int.natCast_mul, Int.add_emod, Int.mul_emod, hr, ← Int.mul_emod, ← Int.add_emod]
    congr 1
    rw [Int.mul_neg]
    omega
  have h3 : (-((a : Int) * x - 1)) % 2 ^ 16 = 0 :=
    Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero h))
  have h4 := h2.trans h3
  change ((a * ((2 ^ 32 - x) % 2 ^ 32 % 2 ^ 16) + 1 : Nat) : Int) % ((2 ^ 16 : Nat) : Int) = 0 at h4
  rw [← Int.natCast_emod] at h4
  exact Int.ofNat_inj.mp h4

/-- `[invO] = -m⁻¹ mod 2¹⁶` for the odd word at `[mo]`. -/
theorem setupInverse_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {mo : Nat}
    (hmo : mo + 4 ≤ size) (h16 : mo < 2 ^ 16) (h4 : 4 ≤ size) (hodd : w32 s.mem base mo % 2 = 1) :
    WP isa (.block (setupInverse mo)) s fun t => Ws t base size ∧
      (w32 s.mem base mo * w32 t.mem base invO + 1) % 2 ^ 16 = 0 ∧ Outside base invO 4 s.mem t.mem ∧
      Rest [.r1, .r2, .r4, .r5, .r6, .r7] s t ∧ t.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
  have hnw := hs.nowrap
  simp only [setupInverse, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ptr (d := .r1) (by decide) h16 fun s₁ u₁ => ?_
  have w₁ := hs.of_upd u₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (d := 0) (K := mo) (by rw [u₁.gpr, u₁.other .r12 (by decide)]) (by omega))
    (w₁.read (d := mo + 0) (n := 4) (by omega)) fun s₂ u₂ => ?_
  refine wp_movw fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun t₀ u₀ => ?_
  have K₀ : Rest [.r1, .r2, .r4, .r5, .r6, .r7] s t₀ := (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide)))).trans (u₀.rest (by decide))
  have m₀ : t₀.mem = s.mem := by rw [u₀.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r6₀ : t₀.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    simp only [u₀.get, u₄.get, u₃.get, reduceCtorEq, ↓reduceIte]
  have r5₀ : (t₀.gpr .r5).toNat = w32 s.mem base mo % 2 ^ 16 := by
    simp only [u₀.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte, dpVal]
    rw [VG.Proof.X25519.Arm.toNat_and_mask16, u₁.mem, Nat.add_zero]
  have r7₀ : t₀.gpr .r7 = t₀.gpr .r5 := by
    simp only [u₀.get, u₄.get, reduceCtorEq, ↓reduceIte]
  have e₀ : (((t₀.gpr .r5).toNat : Int) * (t₀.gpr .r7).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [r7₀]
    have h1 := odd_sq (t₀.gpr .r5).toNat (by rw [r5₀]; omega)
    have h2 : (((t₀.gpr .r5).toNat : Int) * (t₀.gpr .r5).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((t₀.gpr .r5).toNat : Int) * (t₀.gpr .r5).toNat - 1) % 8 = 0
    omega
  refine VG.Proof.X25519.Arm.WP.append (newton_step_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨e₁, k₁, hm₁⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (newton_step_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨e₂, k₂, hm₂⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (newton_step_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨e₃, k₃, hm₃⟩ => ?_
  have e₃' := emod_pow_weaken (i := 16) (by decide) e₃
  have K₃' : Rest [.r2, .r4, .r7] t₀ t₃ := (k₁.trans k₂).trans k₃
  have K₃ : Rest [.r1, .r2, .r4, .r5, .r6, .r7] t₀ t₃ := K₃'.mono (by decide)
  rw [K₃'.gpr .r5 (by decide)] at e₃'
  have w₃ := hs.of_rest (K₀.trans K₃) (by decide)
  refine wp_mov (op2_imm (by decide)) fun t₄ u₄' => wp_dp (op2_reg _ _) fun t₅ u₅ => wp_dp (op2_reg _ _) fun t₆ u₆ => ?_
  have w₆ := ((w₃.of_upd u₄' (by decide)).of_upd u₅ (by decide)).of_upd u₆ (by decide)
  refine wp_str (by decide) (w₆.ea12 (d := 0) (by omega)) (w₆.write (d := 0) (n := 4) (by omega)) fun t m =>
    WP.block_nil ⟨w₆.of_mupd m, ?_, ?_, ?_, ?_⟩
  · have r6₃ : t₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₃'.gpr _ (by decide)]; exact r6₀
    have v : (t₆.gpr .r4).toNat = (2 ^ 32 - (t₃.gpr .r7).toNat) % 2 ^ 32 % 2 ^ 16 := by
      simp only [u₆.get, u₅.get, u₄'.get, reduceCtorEq, ↓reduceIte, dpVal, r6₃]
      rw [VG.Proof.X25519.Arm.toNat_and_mask16, BitVec.toNat_sub]
      rfl
    have hv := neg_inv16 (t₃.gpr .r7).isLt e₃'
    rw [r5₀, ← v] at hv
    show (w32 s.mem base mo * w32 t.mem base 0 + 1) % 2 ^ 16 = 0
    rw [m.mem, w32_write_self, Nat.add_mod, ← Nat.mod_mul_mod, ← Nat.add_mod]
    exact hv
  · rw [m.mem, u₆.mem, u₅.mem, u₄'.mem, hm₃, hm₂, hm₁, m₀]
    exact writeW32_outside _ _ _ (by decide)
  · exact (K₀.trans K₃).trans ((((u₄'.rest (by decide)).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))).trans
      (m.rest _))
  · rw [m.gpr, u₆.other .r6 (by decide), u₅.other .r6 (by decide), u₄'.other .r6 (by decide), K₃'.gpr _ (by decide)]
    exact r6₀

end VG.Proof.Mont.Arm.Dyn
