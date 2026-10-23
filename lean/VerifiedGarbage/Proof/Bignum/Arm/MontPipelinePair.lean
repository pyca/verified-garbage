module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.MontState
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Rounds of two rows

A round may do the rows of two words of the first operand at once (the
operand's word count is even): its contract is `RoundPost`'s, with the
header two rounds on and the accumulator divided by `2⁶⁴` after adding both
words' products and a two-word multiple of the modulus. Its loop reaches the
same invariant as a loop of single rounds. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure PairPost (s t : State) (base : BitVec 32) (tmp a b mod acc n i : Nat) (inv : BitVec 32) : Prop where
  hdr : RoundMeta t.mem base tmp a b mod acc n (i + 2) inv
  ptr : t.gpr .r0 = base + BitVec.ofNat 32 tmp
  value : ∃ q < 2 ^ 64, 2 ^ 64 * val32 t.mem (State.addr base) acc (n + 2) =
    val32 s.mem (State.addr base) acc (n + 2) +
      (w32 s.mem (State.addr base) (a + 4 * i) + 2 ^ 32 * w32 s.mem (State.addr base) (a + 4 * i + 4)) *
        val32 s.mem (State.addr base) b n +
      q * val32 s.mem (State.addr base) mod n
  bound : val32 t.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n
  outside : Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp + 16, 8)] s.mem t.mem
  zero : t.z = decide (i + 2 = n)
  rest : Rest roundClobbers s t

/-- A round of two rows, from an even round index. -/
def PairLaw (round : Prog isa) : Prop :=
  ∀ (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32},
    RoundCtx s base size tmp a b mod acc n → n % 2 = 0 →
    RoundMeta s.mem base tmp a b mod acc n i inv → i + 2 ≤ n →
    s.gpr .r0 = base + BitVec.ofNat 32 tmp →
    val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n →
    val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n →
    (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0 →
    WP isa round s fun t => PairPost s t base tmp a b mod acc n i inv

/-- `round_step` for two rows. -/
theorem pair_step {P T T' a b u m A : Nat} (h : 2 ^ 64 * T' = T + a * b + u * m)
    (hI : P * T % m = A * b % m) : P * 2 ^ 64 * T' % m = (A + P * a) * b % m := by
  have e : P * 2 ^ 64 * T' = P * T + P * a * b + P * u * m := by
    rw [Nat.mul_assoc, h, Nat.mul_add, Nat.mul_add, Nat.mul_assoc P a, Nat.mul_assoc P u]
  rw [e, Nat.add_mul_mod_self_right, Nat.add_mod, hI, ← Nat.add_mod, Nat.add_mul]

/-- Two rows keep the accumulator below `2m`. -/
theorem pair_lt {T T' A b U m : Nat} (h : 2 ^ 64 * T' = T + A * b + U * m) (hT : T < 2 * m)
    (hA : A < 2 ^ 64) (hb : b < m) (hU : U < 2 ^ 64) : T' < 2 * m := by
  have h1 : A * b ≤ (2 ^ 64 - 1) * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : U * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have : 2 ^ 64 * T' < 2 ^ 64 * (2 * m) := by omega
  exact Nat.lt_of_mul_lt_mul_left this

theorem pairBody_ok (round : Prog isa) (law : PairLaw round) {s0 s : State} {base : BitVec 32}
    {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s0 base size tmp a b mod acc n) (even : n % 2 = 0)
    (h : MontInv s0 base tmp a b mod acc n i inv s) (hi : i + 2 ≤ n)
    (hB : val32 s0.mem (State.addr base) b n < val32 s0.mem (State.addr base) mod n)
    (hInv : (val32 s0.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa round s fun t => MontInv s0 base tmp a b mod acc n (i + 2) inv t ∧
      t.z = decide (i + 2 = n) := by
  have nowrap := ctx.workspace.nowrap
  have fa := ctx.aFits
  have fb := ctx.bFits
  have fm := ctx.mFits
  have aa := ctx.accA
  have ab := ctx.accB
  have am := ctx.accM
  have ta := ctx.tmpA
  have tb := ctx.tmpB
  have tm := ctx.tmpM
  have oldB := h.outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldM := h.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldA0 := outs_word32 h.outside (d := a + 4 * i) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldA1 := outs_word32 h.outside (d := a + 4 * i + 4) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  refine WP.mono (law s (ctx.congr h.rest.wr) even h.hdr hi h.ptr
    (by rw [oldM]; exact h.bound) (by rw [oldB, oldM]; exact hB) (by rw [oldM]; exact hInv)) ?_
  intro t post
  obtain ⟨q, _, value⟩ := post.value
  rw [oldA0, oldA1, oldB, oldM] at value
  refine ⟨⟨by omega, post.hdr, post.ptr, ?_, ?_, h.outside.trans post.outside,
    h.rest.trans post.rest⟩, post.zero⟩
  · have pw : 2 ^ (32 * (i + 2)) = 2 ^ (32 * i) * 2 ^ 64 := by
      rw [show 32 * (i + 2) = 32 * i + 64 by omega]; exact Nat.pow_add 2 (32 * i) 64
    have va : val32 s0.mem (State.addr base) a (i + 2) = val32 s0.mem (State.addr base) a i +
        2 ^ (32 * i) * (w32 s0.mem (State.addr base) (a + 4 * i) +
          2 ^ 32 * w32 s0.mem (State.addr base) (a + 4 * i + 4)) := by
      rw [val32_append]
      simp only [val32, Nat.mul_zero, Nat.add_zero]
    rw [pw, va]
    exact pair_step value h.value
  · simpa only [oldM] using post.bound

theorem pair_rounds_ok (round : Prog isa) (law : PairLaw round) (s : State) {base : BitVec 32}
    {size tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (even : n % 2 = 0)
    (hdr : RoundMeta s.mem base tmp a b mod acc n 0 inv)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (hzero : val32 s.mem (State.addr base) acc (n + 2) = 0)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.rounds round) s (MontInv s base tmp a b mod acc n n inv) := by
  have hn := ctx.count
  let loopInv := fun k t => ∃ i, i + 2 * k = n ∧ 0 < k ∧ MontInv s base tmp a b mod acc n i inv t
  unfold VG.Impl.Bignum.Arm.MontPipeline.rounds
  refine WP.loop (M := isa) loopInv ?_ (n / 2) s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (pairBody_ok round law ctx even hi (by omega) hB hInv) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 2 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 2, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, by omega, ?_⟩
    refine ⟨by omega, hdr, ptr, ?_, ?_, Outs.refl _ _ _, Rest.refl _ _⟩
    · rw [hzero]
      simp only [val32, Nat.mul_zero, Nat.zero_mul, Nat.zero_mod]
    · rw [hzero]
      omega

end VG.Proof.Bignum.Arm.MontPipeline
