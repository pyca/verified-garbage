module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on PPC64LE: the rounds

A round (`round_ok`, `MontFios.lean`) replaces the accumulator `T` (`w + 1`
words) with `(T + aᵢ b + u m) / 2⁶⁴`, for the word `aᵢ` at the pointer `r6`,
which it advances; the `w` rounds (`rounds_ok`) leave `T < 2m` with `T 2^(64
w) ≡ a b (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum (round_lt round_step round_sum_lt)

/-- The `w` rounds (`rounds`), counted by `r4` from `w`, over the words of
`a` (at `da` of `B`, pointed to by `r6`), from the accumulator 0: `T < 2m`
and `T 2^(64 w) ≡ a b (mod m)`, for `b < m` (`w` words each, at `dB` and
`dM`), only the accumulator's `w + 2` words changed. -/
theorem rounds_ok {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s₀ B Z)
    (h6 : s₀.gpr .r6 = off B da) (h8 : s₀.gpr .r8 = off B dA) (h7 : s₀.gpr .r7 = off B dB)
    (h10 : s₀.gpr .r10 = off B dM) (h11 : s₀.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s₀.gpr .r4 = BitVec.ofNat 64 w)
    (hinv : ((word s₀.mem B dM).toNat % 2 ^ 32 * (s₀.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dM)
    (hz : wordsVal s₀.mem B dA (w + 1) = 0) (hb : wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w) :
    WP isa rounds s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem) ∧ Keep (roundRegs ++ ([.r4] : List Reg)) s₀ s := by
  have hnw := hs.nowrap
  let M := wordsVal s₀.mem B dM w
  let Bv := wordsVal s₀.mem B dB w
  let J : Nat → State → Prop := fun i s =>
    s.gpr .r6 = off B (da + 8 * i) ∧ Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧
    wordsVal s.mem B dA (w + 1) < 2 * M ∧
    2 ^ (64 * i) * wordsVal s.mem B dA (w + 1) % M = wordsVal s₀.mem B da i * Bv % M ∧
    Keep (roundRegs ++ ([.r4] : List Reg)) s₀ s
  have hJ0 : J 0 s₀ := by
    refine ⟨by rw [h6]; rfl, Outside.refl _ _ _ _, by rw [hz]; omega_arith, by rw [hz]; simp [wordsVal],
      Keep.refl _ _⟩
  refine wp_countdown (body := .seq round (.block [.subi .r4 .r4 1])) (cnt := .r4) (N := w)
    (by omega_arith) (by omega_arith) J (fun i hi s hJ hc => ?_) hJ0 h4 |>.mono
    fun s ⟨_, jout, jlt, jeq, jk⟩ => ⟨⟨jlt, jeq, jout⟩, jk⟩
  obtain ⟨j6, jout, jlt, jeq, jk⟩ := hJ
  have keep : ∀ r ∈ [Reg.r7, .r8, .r10, .r11, .r12], s.gpr r = s₀.gpr r := fun r hr =>
    jk.gpr r (by revert r hr; decide)
  have vM : wordsVal s.mem B dM w = M := jout.wordsVal (by omega_arith) (by omega_arith)
  have vB : wordsVal s.mem B dB w = Bv := jout.wordsVal (by omega_arith) (by omega_arith)
  have wM : word s.mem B dM = word s₀.mem B dM := jout.word (by omega_arith) (by omega_arith)
  have wa : word s.mem B (da + 8 * i) = word s₀.mem B (da + 8 * i) := jout.word (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (round_ok (dA := dA) (dB := dB) (dM := dM) (hs.congr jk.wr) j6
    (by rw [keep .r7 (by decide), h7]) (by rw [keep .r8 (by decide), h8])
    (by rw [keep .r10 (by decide), h10]) (by rw [keep .r11 (by decide), h11])
    (by rw [keep .r12 (by decide), wM]; exact hinv)
    (by omega_arith) hw' (by omega_arith) (by omega_arith) hB hM (by omega_arith) (by omega_arith))
    fun s₁ ⟨⟨k6, kout, u, hu, keq⟩, k₁⟩ => ?_)
  refine WP.mono (subi_ok s₁ .r4 (by decide)) fun s₂ e => ?_
  subst e
  rw [vM, vB, wa] at keq
  have hM0 : 0 < M := by omega_arith
  refine ⟨⟨by gsimp; rw [k6, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_, ?_⟩, ?_⟩
  · gsimp; exact jout.trans (kout.mono (Nat.le_refl _) (by omega_arith))
  · gsimp; exact round_lt keq jlt (s₀.mem.readW _ 64).isLt hb hu
  · gsimp
    rw [wordsVal_succ_top s₀.mem B da i, Nat.mul_succ, Nat.pow_add]
    exact round_step keq jeq
  · have k₂ : Keep [.r4] s₁ (s₁.write .r4 (s₁.gpr .r4 - BitVec.ofNat 64 1)) := Keep.write _ _ _
    exact jk.trans' ((k₁.mono (by decide)).trans' (k₂.mono (by decide)))
  · gsimp
    rw [k₁.gpr _ (by decide)]

end VG.Proof.Bignum.PPC64LE
