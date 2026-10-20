module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.RoundLoop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.AddS
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Finalize
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on AArch64: the branch on the length

`Short.check` sets `x9`, and the code branches on it to `Short.lean`'s code
for `lo sve` to 256 bytes. Every part's proof starts from the state on entry; the
state after `check` differs from it only in `x9`, which no precondition or
postcondition mentions (`Agree`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Short

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Short
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_subImm wp_lsr eval_zero ofNat_beq_zero sub_ofNat)
open VG.Proof.ChaCha20Poly1305.AArch64 (wp_orr)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)

variable {e : Bool}

/-- `s₁` is `s₀` but for `x9` and `x10`. -/
structure Agree (s₀ s₁ : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r
  mem : s₁.mem = s₀.mem
  v : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  sp : s₁.sp = s₀.sp
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr

theorem APre.agree {s₀ s₁ : State} (h : Agree s₀ s₁) (hp : APre e s₀) : APre e s₁ := by
  have h0 := h.gpr .x0 (by decide) (by decide)
  have h1 := h.gpr .x1 (by decide) (by decide)
  have h2 := h.gpr .x2 (by decide) (by decide)
  have h3 := h.gpr .x3 (by decide) (by decide)
  have h4 := h.gpr .x4 (by decide) (by decide)
  have h5 := h.gpr .x5 (by decide) (by decide)
  have h6 := h.gpr .x6 (by decide) (by decide)
  have h7 := h.gpr .x7 (by decide) (by decide)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [kR, nR, aR, dR, tR, ctxR, kp, np, ad, AL, dp, L, tp, cx, h.rd, h.wr, h0, h1, h2, h3, h4, h5,
      h6, h7] <;>
    with_reducible assumption

theorem inv0_agree {s₀ s₁ s : State} (h : Agree s₀ s₁) (hi : Inv0 s₁ s) : Inv0 s₀ s := by
  have h4 := h.gpr .x4 (by decide) (by decide)
  have h5 := h.gpr .x5 (by decide) (by decide)
  have h7 := h.gpr .x7 (by decide) (by decide)
  obtain ⟨x21, un, sp, rd, wr, sv, fr⟩ := hi
  refine ⟨by rw [x21, cx, cx, h7], fun r hr => ?_, by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr],
    fun p hp => ?_, ?_⟩
  · have hu : ∀ r ∈ untouched, r ≠ .x9 ∧ r ≠ .x10 := by decide
    rw [un r hr, h.gpr r (hu r hr).1 (hu r hr).2]
  · have hs : ∀ p ∈ saved, p.1 ≠ .x9 ∧ p.1 ≠ .x10 := by decide
    have := sv p hp
    simp only [cx, h7] at this
    rw [cx, this, h.gpr p.1 (hs p hp).1 (hs p hp).2]
  · simp only [workR, sub, dR, cx, dp, L, h4, h5, h7, h.mem] at fr ⊢
    exact fr

theorem MainS.agree {s₀ s₁ s : State} (h : Agree s₀ s₁) (hm : MainS s₁ s) : MainS s₀ s := by
  have h0 := h.gpr .x0 (by decide) (by decide)
  have h1 := h.gpr .x1 (by decide) (by decide)
  have h2 := h.gpr .x2 (by decide) (by decide)
  have h3 := h.gpr .x3 (by decide) (by decide)
  have h4 := h.gpr .x4 (by decide) (by decide)
  have h5 := h.gpr .x5 (by decide) (by decide)
  have h7 := h.gpr .x7 (by decide) (by decide)
  obtain ⟨i, v, p, c⟩ := hm
  refine ⟨inv0_agree h i, fun r hr => by rw [v r hr, h.v r hr], ?_, ?_⟩
  · simp only [otk, K, N, A, D, kp, np, ad, AL, dp, L, cx, h0, h1, h2, h3, h4, h5, h7, h.mem] at p ⊢
    exact p
  · simp only [K, N, D, kp, np, dp, L, h0, h1, h4, h5, h.mem] at c ⊢
    exact c

theorem MainO.agree {s₀ s₁ s : State} (h : Agree s₀ s₁) (hm : MainO s₁ s) : MainO s₀ s := by
  have h0 := h.gpr .x0 (by decide) (by decide)
  have h1 := h.gpr .x1 (by decide) (by decide)
  have h2 := h.gpr .x2 (by decide) (by decide)
  have h3 := h.gpr .x3 (by decide) (by decide)
  have h4 := h.gpr .x4 (by decide) (by decide)
  have h5 := h.gpr .x5 (by decide) (by decide)
  have h7 := h.gpr .x7 (by decide) (by decide)
  obtain ⟨i, v, t, p⟩ := hm
  refine ⟨inv0_agree h i, fun r hr => by rw [v r hr, h.v r hr], ?_, ?_⟩
  · simp only [otk, K, N, A, D, kp, np, ad, AL, dp, L, cx, h0, h1, h2, h3, h4, h5, h7, h.mem] at t ⊢
    exact t
  · simp only [K, N, D, kp, np, dp, L, h0, h1, h4, h5, h.mem] at p ⊢
    exact p

/-- The value `check sve` leaves in `x9`. -/
abbrev checkVal (sve : Bool) (x : BitVec 64) : BitVec 64 :=
  ((x - BitVec.ofNat 64 1) >>> 8) ||| ((x - BitVec.ofNat 64 (lo sve)) >>> 8)

/-- `x9`, zero iff `lo sve ≤ len ≤ 256`. -/
theorem check_ok (sve : Bool) (s₀ : State) :
    WP isa (.block (check sve)) s₀ fun s₁ => Agree s₀ s₁ ∧ s₁.gpr .x9 = checkVal sve (s₀.gpr .x5) := by
  have hlo : lo sve < 4096 := by cases sve <;> decide
  have h : WP isa (.block (check sve)) s₀ fun s₁ => (∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .x9 = checkVal sve (s₀.gpr .x5) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr :=
    wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_subImm hlo fun s₃ u₃ =>
      wp_lsr (by decide) fun s₄ u₄ => wp_orr fun s₅ u₅ => WP.block_nil
      ⟨fun r h9 h10 => by rw [u₅.other r h9, u₄.other r h10, u₃.other r h10, u₂.other r h9, u₁.other r h9],
        by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr,
          u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.preservedV (WP.withSp h) (by cases sve <;> lit_decide))
    fun s₁ ⟨⟨⟨g, x9, m, rd, wr⟩, sp⟩, v⟩ => ⟨⟨g, m, v, sp, rd, wr⟩, x9⟩

theorem checkVal_eq (sve : Bool) {L : Nat} (h : L < 2 ^ 64) :
    (checkVal sve (BitVec.ofNat 64 L) == 0) = decide (lo sve ≤ L ∧ L ≤ 256) := by
  have hz : ∀ x : BitVec 64, (x == 0) = decide (x.toNat = 0) := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    · have : x.toNat ≠ 0 := fun h' => hx (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (x == 0) = false from beq_eq_false_iff_ne.mpr hx]
      simp [this]
  rw [hz]
  congr 1
  apply propext
  cases sve <;>
  simp only [checkVal, lo, BitVec.toNat_or, Nat.or_eq_zero_iff, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Bool.false_eq_true, ite_true, ite_false] <;>
  omega

/-- The branch: to `Short.lean`'s code iff `lo sve ≤ len ≤ 256`. -/
theorem check_eval {sve : Bool} {s₀ s₁ : State} (h : s₁.gpr .x9 = checkVal sve (s₀.gpr .x5)) :
    isa.eval (.zero .x .x9) s₁ = some (decide (lo sve ≤ L s₀ ∧ L s₀ ≤ 256)) := by
  have e : isa.eval (.zero .x .x9) s₁ = some (s₁.gpr .x9 == 0) := eval_zero s₁ .x9
  rw [e, h, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, checkVal_eq sve (s₀.gpr .x5).isLt]

end VG.Proof.ChaCha20Poly1305.AArch64.Short
