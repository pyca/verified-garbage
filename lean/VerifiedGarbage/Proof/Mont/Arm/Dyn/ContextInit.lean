module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context

import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: setting up the context

`contextSetup umaal n`, for the odd modulus `m > 1` in slot 0, stores `m'`,
one in slot 6 and `R² mod m` in slot 7 (`contextSetup_ok`): `2ⁿ R` by
doublings, then six Montgomery squarings, each of which squares the power of
two beside `R` (`mont_square`, `rSquared_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest)

variable {umaal : Bool}

/-- The memory the setup changes. -/
def setupRanges (n : Nat) : List (Nat × Nat) :=
  [(0, 4), (slot n 6, 8 * n), (slot n 7, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

/-- The low digit of a number is its low word's. -/
theorem val32_mod16 (m : Mem) (base : Addr) (d k : Nat) (hk : 0 < k) :
    val32 m base d k % 2 ^ 16 = w32 m base d % 2 ^ 16 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_using [hk]⟩
  rw [val32, Nat.add_mod, show 2 ^ 32 * val32 m base (d + 4) k = 2 ^ 16 * (2 ^ 16 * val32 m base (d + 4) k) by
    rw [← Nat.mul_assoc], Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]

/-- A Montgomery square of `2^e R mod m` is `2^(2e) R mod m`. -/
theorem mont_square {v e n m : Nat} (hc : Nat.Coprime (2 ^ (64 * n)) m) (hv : v < m)
    (h : v * 2 ^ (64 * n) % m = (2 ^ e * 2 ^ (64 * n) % m) * (2 ^ e * 2 ^ (64 * n) % m) % m) :
    v = 2 ^ (2 * e) * 2 ^ (64 * n) % m := by
  have he : v % m = 2 ^ (2 * e) * 2 ^ (64 * n) % m := VG.Proof.Bignum.mont_cancel hc (by
    rw [h, ← Nat.mul_mod, show 2 * e = e + e by omega_using [], Nat.pow_add]
    exact congrArg (· % m) (by grind))
  rwa [Nat.mod_eq_of_lt hv] at he

/-- The invariant of the squarings after `i` of them. -/
structure SqInv (n m : Nat) (base : Addr) (size : Nat) (s : State) (i : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n 7) (2 * n) = 2 ^ (n * 2 ^ i) * 2 ^ (64 * n) % m
  mem : Outs base (opRanges n 7) s.mem u.mem
  rest : Rest (.lr :: dclob) s u
  lr : u.gpr .lr = BitVec.ofNat 32 (6 - i)

/-- `[slot 7] = R² mod m`: `2ⁿ R` by doublings, squared six times. -/
theorem rSquared_ok {n m size : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (h128 : 128 * n < 2 ^ 16) :
    WP isa (rSquared umaal n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m ∧ Outs base (opRanges n 7) s.mem t.mem ∧
      Rest (.lr :: dclob) s t := by
  have hn := h.n0
  have hm0 : 0 < m := by have := h.gt_one; omega_using [this]
  unfold rSquared
  rw [show squarings = 6 from rfl]
  refine WP.seq (WP.mono (powerTwo_ok h (o := 7) (by decide) (by omega_using [hn]) (by omega_using [h128]))
    fun t₀ ⟨c₀, V₀, O₀, R₀⟩ => ?_)
  refine WP.seq (VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 6) (by decide)))
    fun t₁ u₁ => WP.block_nil ?_)
  have I0 : SqInv n m base size s 0 t₁ := by
    refine ⟨⟨c₀.ws.of_upd u₁ (by decide), c₀.size_le, c₀.small, c₀.n0, by rw [u₁.mem]; exact c₀.modulus, c₀.gt_one,
      by rw [u₁.mem]; exact c₀.inverse⟩, ?_, ?_, ?_, ?_⟩
    · rw [u₁.mem, V₀, ← Nat.pow_add]
      exact congrArg (2 ^ · % m) (by omega_using [])
    · rw [u₁.mem]; exact O₀
    · exact R₀.trans (u₁.rest (by decide))
    · rw [u₁.gpr]
  refine WP.loop (M := isa) (fun r u => ∃ i, r = 6 - i ∧ i < 6 ∧ SqInv n m base size s i u) ?_
    6 t₁ ⟨0, rfl, by decide, I0⟩
  rintro r u ⟨i, rfl, hi, I⟩
  have hv : val32 u.mem base (slot n 7) (2 * n) < m := by rw [I.val]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok I.ctx (o := 7) (a := 7) (b := 7) (by decide) (by decide) (by decide) hv)
    fun u₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  refine VG.Proof.X25519.Arm.wp_subs (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 1) (by decide)))
    fun u₂ v₂ z₂ => WP.block_nil ?_
  have I' : SqInv n m base size s (i + 1) u₂ := by
    refine ⟨⟨c₁.ws.of_upd v₂ (by decide), c₁.size_le, c₁.small, c₁.n0, by rw [v₂.mem]; exact c₁.modulus, c₁.gt_one,
      by rw [v₂.mem]; exact c₁.inverse⟩, ?_, ?_, ?_, ?_⟩
    · rw [v₂.mem, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]
      exact mont_square I.ctx.coprime lt₁ (by rw [V₁, I.val])
    · rw [v₂.mem]; exact I.mem.trans K₁.mem
    · exact (I.rest.trans (K₁.rest.mono (by decide))).trans (v₂.rest (by decide))
    · rw [v₂.gpr, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega_using [hi]) (by omega_using [])]
      congr 1
  have hz : u₂.z = decide (i + 1 = 6) := by
    rw [z₂, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega_using [hi]) (by omega_using []),
      VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_using [])]
    simp only [decide_eq_decide]
    omega_using [hi]
  by_cases hi1 : i + 1 = 6
  · refine .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hi1]; rfl, I'.ctx, ?_, I'.mem, I'.rest⟩
    rw [I'.val, hi1, ← Nat.pow_add]
    exact congrArg (2 ^ · % m) (by omega_using [])
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hi1]; rfl, 6 - (i + 1),
      by omega_using [hi], i + 1, rfl, by omega_using [hi, hi1], I'⟩

theorem contextSetup_ok {n size m : Nat} {base : Addr} {s : State} (hs : Ws s base size) (hn : 0 < n)
    (hz : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16) (h128 : 128 * n < 2 ^ 16)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (contextSetup umaal n) s fun t => Context n m base size t ∧ val32 t.mem base (slot n 6) (2 * n) = 1 ∧
      val32 t.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m ∧ Outs base (setupRanges n) s.mem t.mem ∧
      Rest (.lr :: dclob) s t := by
  have nw := hs.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  have low : w32 s.mem base (slot n 0) % 2 ^ 16 = m % 2 ^ 16 := by rw [← hv, val32_mod16 _ _ _ _ (by omega_using [hn])]
  unfold contextSetup
  refine WP.seq (WP.mono (setupInverse_ok hs (mo := modS n) (by simp only [modS, stride] at *; omega_using [hz, b0])
    (by simp only [modS, stride] at *; omega_using [h16, b0]) (by omega_using [hz, b0, h0]) (by simp only [modS]; omega_using [hodd, low])) fun t₁ ⟨w₁, I₁, O₁, R₁, _⟩ => ?_)
  have c₁ : Context n m base size t₁ := by
    refine ⟨w₁, hz, h16, hn, ?_, hm1, ?_⟩
    · rw [O₁.val32 (by simp only [invO]; omega_using [h0]) (by simp only [stride] at *; omega_using [h16, b0])]; exact hv
    · rw [Nat.add_mod, Nat.mul_mod, ← low, ← Nat.mul_mod, ← Nat.add_mod]; exact I₁
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  refine WP.seq (WP.mono (one_ok w₁ (n := n) (out := oneS n) hn (by simp only [oneS, stride] at *; omega_using [hz, b6])
    (by simp only [oneS, stride] at *; omega_using [h16, b6])) fun t₂ ⟨w₂, V₂, O₂, R₂⟩ => ?_)
  have K₂ : OpKeep n base 6 t₁ t₂ := ⟨R₂.mono (by decide), Outs.of_outside O₂ (by simp [oneS])⟩
  have c₂ := c₁.keep (by omega_using []) w₂ K₂
  refine WP.mono (rSquared_ok c₂ h128) fun t ⟨c, V, O, R⟩ => ⟨c, ?_, V, ?_, ?_⟩
  · have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_using [hz, nw]
    rw [slot_val32 O (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw']; exact V₂
  · refine ((Outs.of_outside O₁ (by simp [setupRanges, invO])).trans
      (Outs.of_outside O₂ (by simp [setupRanges, oneS]))).trans (O.mono ?_)
    intro r hr; simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [setupRanges]
  · exact ((R₁.mono (by decide)).trans (R₂.mono (by decide))).trans R

end VG.Proof.Mont.Arm.Dyn
