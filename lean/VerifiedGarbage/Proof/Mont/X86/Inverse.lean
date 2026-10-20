module

public import VerifiedGarbage.Impl.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Runtime Montgomery inverse correctness on 32-bit x86 -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86
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

/-- Negation of an inverse modulo 2³². -/
theorem neg_inv {a x : Nat} (hx : x < 2 ^ 32) (h : ((a : Int) * x - 1) % (2 ^ 32 : Int) = 0) :
    (a * ((2 ^ 32 - x + 0) % 2 ^ 32) + 1) % 2 ^ 32 = 0 := by
  have hr : (((2 ^ 32 - x + 0) % 2 ^ 32 : Nat) : Int) % 2 ^ 32 = -(x : Int) % 2 ^ 32 := by
    rw [Int.natCast_emod, show ((2 ^ 32 : Nat) : Int) = 2 ^ 32 from rfl, Int.emod_emod]
    omega
  have h2 : ((a * ((2 ^ 32 - x + 0) % 2 ^ 32) + 1 : Nat) : Int) % 2 ^ 32 =
      (-((a : Int) * x - 1)) % 2 ^ 32 := by
    rw [Int.natCast_add, Int.natCast_mul, Int.add_emod, Int.mul_emod, hr, ← Int.mul_emod,
      ← Int.add_emod]
    congr 1
    rw [Int.mul_neg]
    omega
  have h3 : (-((a : Int) * x - 1)) % 2 ^ 32 = 0 :=
    Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero h))
  have h4 := h2.trans h3
  change ((a * ((2 ^ 32 - x + 0) % 2 ^ 32) + 1 : Nat) : Int) % ((2 ^ 32 : Nat) : Int) = 0 at h4
  rw [← Int.natCast_emod] at h4
  exact Int.ofNat_inj.mp h4


theorem newton_val (a x : BitVec 32) :
    ((BitVec.ofNat 32 (x.toNat * (2 - BitVec.ofNat 32 (a.toNat * x.toNat)).toNat)).toNat : Int) % 2 ^ 32 =
      ((x.toNat : Int) * (2 - (a.toNat : Int) * x.toNat)) % 2 ^ 32 := by
  have ofNat_mod (n : Nat) : ((BitVec.ofNat 32 n).toNat : Int) % 2 ^ 32 = (n : Int) % 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Int.natCast_emod]
    exact Int.emod_emod _ _
  have sub_mod (y : BitVec 32) : ((2 - y).toNat : Int) % 2 ^ 32 = (2 - (y.toNat : Int)) % 2 ^ 32 := by
    rw [BitVec.toNat_sub, show (2 : BitVec 32).toNat = 2 from rfl,
      Int.natCast_emod, show ((2 ^ 32 : Nat) : Int) = 2 ^ 32 from rfl, Int.emod_emod]
    have hy := y.isLt
    omega
  rw [ofNat_mod, Int.natCast_mul, Int.mul_emod, sub_mod,
    Int.sub_emod, ofNat_mod, Int.natCast_mul, ← Int.sub_emod, ← Int.mul_emod]

/-- The machine step computes Newton's update without changing memory. -/
theorem newton_ok (s : State) :
    WP isa (.block newton) s fun t =>
      (((t.gpr .ecx).toNat : Int) - (s.gpr .ecx).toNat *
        (2 - (s.gpr .ebx).toNat * (s.gpr .ecx).toNat)) % (2 ^ 32 : Int) = 0 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t ∧ t.mem = s.mem := by
  unfold newton
  refine wp_movS rfl fun _s₁ u₁ _ => ?_
  refine wp_mul fun _s₂ m₂ => ?_
  refine wp_movS rfl fun _s₃ u₃ _ => ?_
  refine wp_subS rfl fun _s₄ u₄ _ => ?_
  refine wp_movS rfl fun _s₅ u₅ _ => ?_
  refine wp_mul fun _s₆ m₆ => ?_
  refine wp_movS rfl fun _s₇ u₇ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₇.gpr, m₆.eax, u₅.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide),
      m₂.other .ecx (by decide) (by decide), u₁.other .ecx (by decide),
      u₅.other .ebp (by decide), u₄.gpr, u₃.gpr, u₃.other .eax (by decide),
      m₂.eax, u₁.gpr, u₁.other .ecx (by decide)]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (newton_val _ _)
  · exact (((((u₁.keeps.mono (by decide) |>.widen m₂.keeps).widen u₃.keeps).widen
      u₄.keeps).widen u₅.keeps).widen m₆.keeps).widen u₇.keeps
  · rw [u₇.mem, m₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem]

/-- A machine step doubles the known inverse bits. -/
theorem newton_step_ok (s : State) {j : Nat} (hj : 2 * j ≤ 32)
    (h : (((s.gpr .ebx).toNat : Int) * (s.gpr .ecx).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) s fun t =>
      (((t.gpr .ebx).toNat : Int) * (t.gpr .ecx).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t ∧ t.mem = s.mem :=
  WP.mono (newton_ok s) fun t ⟨hv, k, hm⟩ =>
    ⟨by rw [k.1 .ebx (by decide)]; exact newton_step hj h hv, k, hm⟩

/-- An odd low modulus word yields its negative inverse in `eax`. -/
theorem inverse_ok (s : State) (hodd : (s.gpr .ebx).toNat % 2 = 1) :
    WP isa (.block inverse) s fun t =>
      ((s.gpr .ebx).toNat * (t.gpr .eax).toNat + 1) % 2 ^ 32 = 0 ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t ∧ t.mem = s.mem := by
  unfold inverse
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun t₀ u₀ _ => ?_
  have e₀ : (((t₀.gpr .ebx).toNat : Int) * (t₀.gpr .ecx).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [u₀.gpr, u₀.other .ebx (by decide)]
    have h1 := odd_sq _ hodd
    have h2 : (((s.gpr .ebx).toNat : Int) * (s.gpr .ebx).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((s.gpr .ebx).toNat : Int) * (s.gpr .ebx).toNat - 1) % 8 = 0
    omega
  refine WP.block_append (WP.mono (newton_step_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨e₁, k₁, hm₁⟩ => ?_)
  refine WP.block_append (WP.mono (newton_step_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨e₂, k₂, hm₂⟩ => ?_)
  refine WP.block_append (WP.mono (newton_step_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨e₃, k₃, hm₃⟩ => ?_)
  refine WP.block_append (WP.mono (newton_step_ok t₃ (j := 16) (by decide)
    (emod_pow_weaken (by decide) e₃)) fun t₄ ⟨e₄, k₄, hm₄⟩ => ?_)
  have kk : Keeps [.eax, .ecx, .edx, .ebp] s t₄ :=
    (((u₀.keeps.mono (by decide)).trans k₁).trans k₂).trans k₃ |>.trans k₄
  rw [kk.1 .ebx (by decide)] at e₄
  refine wp_movS rfl fun _t₅ u₅ _ => ?_
  refine wp_subS rfl fun _t₆ u₆ _ => WP.block_nil ⟨?_, (kk.widen u₅.keeps).widen u₆.keeps, ?_⟩
  · rw [u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), BitVec.toNat_sub,
      show (0 : BitVec 32).toNat = 0 from rfl]
    exact neg_inv (t₄.gpr .ecx).isLt e₄
  · rw [u₆.mem, u₅.mem, hm₄, hm₃, hm₂, hm₁, u₀.mem]

/-- Setup reads the low modulus word, computes its inverse, and changes
only the designated four-byte slot in memory. -/
theorem setupInverse_ok {s : State} {base : Addr} {size mo inv : Nat}
    (hs : Scr s base size) (hmo : mo + 4 ≤ size) (hi : inv + 4 ≤ size)
    (hodd : w32 s.mem base mo % 2 = 1) :
    WP isa (.block (setupInverse mo inv)) s fun t =>
      (w32 s.mem base mo * w32 t.mem base inv + 1) % 2 ^ 32 = 0 ∧
      Outside base inv 4 s.mem t.mem ∧ Keeps clob s t := by
  unfold setupInverse
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hmo) fun s₁ u₁ _ => ?_
  refine WP.block_append (WP.mono (inverse_ok s₁ (by rw [u₁.gpr]; exact hodd)) fun s₂ ⟨hv, k₂, hm₂⟩ => ?_)
  have k : Keeps clob s s₂ := (u₁.keeps.mono (by decide)).widen k₂
  have hs₂ := hs.of_keeps k (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write hi) fun t mt => WP.block_nil ⟨?_, ?_, k.widen (mt.keeps [])⟩
  · rw [mt.mem, w32_write_self]
    rw [u₁.gpr] at hv
    exact hv
  · rw [mt.mem, hm₂, u₁.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.Mont.X86.Dynamic
