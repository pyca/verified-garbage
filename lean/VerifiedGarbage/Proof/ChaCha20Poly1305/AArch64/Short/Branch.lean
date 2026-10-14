module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Short
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# ChaCha20-Poly1305 on AArch64: the branch on the length

`Short.check` sets `x9`, and the code branches on it to `Short.lean`'s code
for 1 to 256 bytes. Every part's proof starts from the state on entry; the
state after `check` differs from it only in `x9`, which no precondition or
postcondition mentions (`Agree`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Short

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Short
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_subImm wp_lsr eval_zero ofNat_beq_zero sub_ofNat)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)

variable {e : Bool}

/-- `s₁` is `s₀` but for `x9`. -/
structure Agree (s₀ s₁ : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → s₁.gpr r = s₀.gpr r
  mem : s₁.mem = s₀.mem
  v : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  sp : s₁.sp = s₀.sp
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr

theorem APre.agree {s₀ s₁ : State} (h : Agree s₀ s₁) (hp : APre e s₀) : APre e s₁ := by
  have h0 := h.gpr .x0 (by decide)
  have h1 := h.gpr .x1 (by decide)
  have h2 := h.gpr .x2 (by decide)
  have h3 := h.gpr .x3 (by decide)
  have h4 := h.gpr .x4 (by decide)
  have h5 := h.gpr .x5 (by decide)
  have h6 := h.gpr .x6 (by decide)
  have h7 := h.gpr .x7 (by decide)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [kR, nR, aR, dR, tR, ctxR, kp, np, ad, AL, dp, L, tp, cx, h.rd, h.wr, h0, h1, h2, h3, h4, h5,
      h6, h7] <;>
    with_reducible assumption

theorem inv0_agree {s₀ s₁ s : State} (h : Agree s₀ s₁) (hi : Inv0 s₁ s) : Inv0 s₀ s := by
  have h4 := h.gpr .x4 (by decide)
  have h5 := h.gpr .x5 (by decide)
  have h7 := h.gpr .x7 (by decide)
  obtain ⟨x21, un, sp, rd, wr, sv, fr⟩ := hi
  refine ⟨by rw [x21, cx, cx, h7], fun r hr => ?_, by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr],
    fun p hp => ?_, ?_⟩
  · have hu : ∀ r ∈ untouched, r ≠ .x9 := by decide
    rw [un r hr, h.gpr r (hu r hr)]
  · have hs : ∀ p ∈ saved, p.1 ≠ .x9 := by decide
    have := sv p hp
    simp only [cx, h7] at this
    rw [cx, this, h.gpr p.1 (hs p hp)]
  · simp only [workR, sub, dR, cx, dp, L, h4, h5, h7, h.mem] at fr ⊢
    exact fr

theorem MainS.agree {s₀ s₁ s : State} (h : Agree s₀ s₁) (hm : MainS s₁ s) : MainS s₀ s := by
  have h0 := h.gpr .x0 (by decide)
  have h1 := h.gpr .x1 (by decide)
  have h2 := h.gpr .x2 (by decide)
  have h3 := h.gpr .x3 (by decide)
  have h4 := h.gpr .x4 (by decide)
  have h5 := h.gpr .x5 (by decide)
  have h7 := h.gpr .x7 (by decide)
  obtain ⟨i, v, p, c⟩ := hm
  refine ⟨inv0_agree h i, fun r hr => by rw [v r hr, h.v r hr], ?_, ?_⟩
  · simp only [otk, K, N, A, D, kp, np, ad, AL, dp, L, cx, h0, h1, h2, h3, h4, h5, h7, h.mem] at p ⊢
    exact p
  · simp only [K, N, D, kp, np, dp, L, h0, h1, h4, h5, h.mem] at c ⊢
    exact c

theorem MainO.agree {s₀ s₁ s : State} (h : Agree s₀ s₁) (hm : MainO s₁ s) : MainO s₀ s := by
  have h0 := h.gpr .x0 (by decide)
  have h1 := h.gpr .x1 (by decide)
  have h2 := h.gpr .x2 (by decide)
  have h3 := h.gpr .x3 (by decide)
  have h4 := h.gpr .x4 (by decide)
  have h5 := h.gpr .x5 (by decide)
  have h7 := h.gpr .x7 (by decide)
  obtain ⟨i, v, t, p⟩ := hm
  refine ⟨inv0_agree h i, fun r hr => by rw [v r hr, h.v r hr], ?_, ?_⟩
  · simp only [otk, K, N, A, D, kp, np, ad, AL, dp, L, cx, h0, h1, h2, h3, h4, h5, h7, h.mem] at t ⊢
    exact t
  · simp only [K, N, D, kp, np, dp, L, h0, h1, h4, h5, h.mem] at p ⊢
    exact p

/-- `x9 = (len - 1) >> 8`, zero iff `1 ≤ len ≤ 256`. -/
theorem check_ok (s₀ : State) :
    WP isa (.block check) s₀ fun s₁ => Agree s₀ s₁ ∧
      s₁.gpr .x9 = (s₀.gpr .x5 - BitVec.ofNat 64 1) >>> 8 := by
  have h : WP isa (.block check) s₀ fun s₁ => (∀ r, r ≠ .x9 → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .x9 = (s₀.gpr .x5 - BitVec.ofNat 64 1) >>> 8 ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧
      s₁.wr = s₀.wr :=
    wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil
      ⟨fun r hr => by rw [u₂.other r hr, u₁.other r hr], by rw [u₂.gpr, u₁.gpr], by rw [u₂.mem, u₁.mem],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.withSp h) (by lit_decide)) fun s₁ ⟨⟨⟨g, x9, m, rd, wr⟩, sp⟩, v⟩ =>
    ⟨⟨g, m, v, sp, rd, wr⟩, x9⟩

theorem shr8_ofNat {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 8 = BitVec.ofNat 64 (n / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- The branch: to `Short.lean`'s code iff `1 ≤ len ≤ 256`. -/
theorem check_eval {s₀ s₁ : State} (h : s₁.gpr .x9 = (s₀.gpr .x5 - BitVec.ofNat 64 1) >>> 8) :
    isa.eval (.zero .x .x9) s₁ = some (decide (1 ≤ L s₀ ∧ L s₀ ≤ 256)) := by
  have e : isa.eval (.zero .x .x9) s₁ = some (s₁.gpr .x9 == 0) := eval_zero s₁ .x9
  have hLt : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  rw [e, h, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀]
  by_cases h0 : L s₀ = 0
  · rw [h0]; decide
  · rw [sub_ofNat (by omega), shr8_ofNat (by omega), ofNat_beq_zero (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.ChaCha20Poly1305.AArch64.Short
