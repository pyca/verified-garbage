module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontPass
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on PPC64LE: the rounds

`setup_ok`: `-m⁻¹ mod 2⁶⁴` from `-m⁻¹ mod 2³²` by a step of Newton's
iteration, and `w`. A round (`round_ok`) replaces the accumulator `T` (`w +
1` words) with `(T + aᵢ b + u m) / 2⁶⁴`, for the word `aᵢ` at the pointer
`r6`, which it advances; the `w` rounds (`rounds_ok`) leave `T < 2m` with `T
2^(64 w) ≡ a b (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum (round_lt round_step round_sum_lt)

/-! ## `-m⁻¹ mod 2⁶⁴` -/

/-- A step of Newton's iteration: `m y ≡ -1 (mod 2³²)` gives `m y (2 + m y) ≡
-1 (mod 2⁶⁴)`, since `m y (2 + m y) + 1 = (m y + 1)²`. -/
theorem newton64 (m y : BitVec 64) (h : (m.toNat % 2 ^ 32 * y.toNat + 1) % 2 ^ 32 = 0) :
    (m.toNat * ((m * y + BitVec.ofNat 64 2) * y).toNat + 1) % 2 ^ 64 = 0 := by
  have e : m * ((m * y + BitVec.ofNat 64 2) * y) + 1#64 = (m * y + 1#64) * (m * y + 1#64) := by
    grind
  have hq : (m * y + 1#64).toNat % 2 ^ 32 = 0 := by
    have hm : m.toNat % 2 ^ 32 * y.toNat % 2 ^ 32 = m.toNat * y.toNat % 2 ^ 32 := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [BitVec.toNat_add, BitVec.toNat_mul, show (1#64).toNat = 1 from rfl]
    omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_mul m, BitVec.toNat_mul (m * y + 1#64)] at e'
  obtain ⟨q, hq'⟩ : ∃ q, (m * y + 1#64).toNat = 2 ^ 32 * q := ⟨_, (Nat.div_add_mod _ _).symm.trans (by rw [hq, Nat.add_zero])⟩
  rw [hq', show 2 ^ 32 * q * (2 ^ 32 * q) = 2 ^ 64 * (q * q) by grind, Nat.mul_mod_right,
    show (1#64).toNat = 1 from rfl, Nat.mod_add_mod] at e'
  exact e'

theorem toNat_ofNat_shr1' {n : Nat} (hn : n < 2 ^ 63) : BitVec.ofNat 64 (2 * n) >>> 1 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- `setup`: `-m⁻¹ mod 2⁶⁴` into `r0`, `w` into `r3` and `r4`. -/
theorem setup_ok {s : State} {B : Addr} {Z dM w : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B dM)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : w < 2 ^ 31) (hM : dM + 8 ≤ Z)
    (hinv : ((word s.mem B dM).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block setup) s fun s' =>
      (((word s.mem B dM).toNat * (s'.gpr .r0).toNat + 1) % 2 ^ 64 = 0 ∧ s'.gpr .r3 = BitVec.ofNat 64 w ∧
        s'.gpr .r4 = BitVec.ofNat 64 w ∧ s'.mem = s.mem) ∧ Keep [.r0, .r3, .r4] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h10, h11, hs.ld hM, BitVec.add_zero, toNat_ofNat_shr1' (show w < 2 ^ 63 by omega_arith)]
  exact newton64 _ _ hinv

/-! ## A round -/

theorem round_ok {s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h8 : s.gpr .r8 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h10 : s.gpr .r10 = off B dM) (h3 : s.gpr .r3 = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B dM).toNat * (s.gpr .r0).toNat + 1) % 2 ^ 64 = 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dM)
    (hT : wordsVal s.mem B dA (w + 1) < 2 * wordsVal s.mem B dM w)
    (hb : wordsVal s.mem B dB w < wordsVal s.mem B dM w) :
    WP isa round s fun s' =>
      (s'.gpr .r6 = off B (da + 8) ∧ Outside B dA (8 * (w + 2)) s.mem s'.mem ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal s'.mem B dA (w + 1) =
          wordsVal s.mem B dA (w + 1) + (word s.mem B da).toNat * wordsVal s.mem B dB w +
            u * wordsVal s.mem B dM w) ∧
      Keep passRegs s s' := by
  have hnw := hs.nowrap
  unfold round
  refine WP.seq (WP.mono (mulPass_ok hs h6 h8 h7 h3 (by omega_arith) hw' ha hA hB (by omega_arith))
    fun s₁ ⟨⟨i6, iout, ieq⟩, k₁⟩ => ?_)
  have g : ∀ r ∈ [Reg.r0, .r3, .r8, .r10], s₁.gpr r = s.gpr r := fun r hr => k₁.gpr r (by revert r hr; decide)
  have vM : wordsVal s₁.mem B dM w = wordsVal s.mem B dM w := iout.wordsVal (by omega_arith) (by omega_arith)
  have wM : word s₁.mem B dM = word s.mem B dM := iout.word (by omega_arith) (by omega_arith)
  have hM0 := wordsVal_lt s.mem B dM w
  refine WP.mono (redPass_ok (hs.congr k₁.wr) (by rw [g .r8 (by decide), h8]) (by rw [g .r10 (by decide), h10])
    (by rw [g .r3 (by decide), h3]) hw hw' hA hM dMA (by rw [wM, g .r0 (by decide)]; exact hinv)
    (fun u hu => ?_)) fun s₂ ⟨⟨jout, jeq⟩, k₂⟩ => ?_
  · rw [ieq, vM]
    have h1 := round_sum_lt hT (word s.mem B da).isLt hb hu
    have h2 : 2 ^ 65 * wordsVal s.mem B dM w < 2 ^ (64 * (w + 2)) :=
      calc 2 ^ 65 * wordsVal s.mem B dM w < 2 ^ 65 * 2 ^ (64 * w) := Nat.mul_lt_mul_of_pos_left hM0 (by decide)
        _ = 2 ^ (65 + 64 * w) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ (64 * (w + 2)) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_using [h1, h2]
  refine ⟨⟨by rw [k₂.gpr _ (by decide), i6], iout.trans jout,
    (word s₁.mem B dA).toNat * (s₁.gpr .r0).toNat % 2 ^ 64, Nat.mod_lt _ (by decide), ?_⟩,
    (k₁.trans k₂).mono (by decide)⟩
  rw [jeq, ieq, vM]

/-- The `w` rounds (`rounds`), counted by `r4` from `w`, over the words of
`a` (at `da` of `B`, pointed to by `r6`), from the accumulator 0: `T < 2m`
and `T 2^(64 w) ≡ a b (mod m)`, for `b < m` (`w` words each, at `dB` and
`dM`), only the accumulator's `w + 2` words changed. -/
theorem rounds_ok {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s₀ B Z)
    (h6 : s₀.gpr .r6 = off B da) (h8 : s₀.gpr .r8 = off B dA) (h7 : s₀.gpr .r7 = off B dB)
    (h10 : s₀.gpr .r10 = off B dM) (h3 : s₀.gpr .r3 = BitVec.ofNat 64 w)
    (h4 : s₀.gpr .r4 = BitVec.ofNat 64 w)
    (hinv : ((word s₀.mem B dM).toNat * (s₀.gpr .r0).toNat + 1) % 2 ^ 64 = 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dM)
    (hz : wordsVal s₀.mem B dA (w + 1) = 0) (hb : wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w) :
    WP isa rounds s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem) ∧ Keep (passRegs ++ ([.r4] : List Reg)) s₀ s := by
  have hnw := hs.nowrap
  let M := wordsVal s₀.mem B dM w
  let Bv := wordsVal s₀.mem B dB w
  let J : Nat → State → Prop := fun i s =>
    s.gpr .r6 = off B (da + 8 * i) ∧ Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧
    wordsVal s.mem B dA (w + 1) < 2 * M ∧
    2 ^ (64 * i) * wordsVal s.mem B dA (w + 1) % M = wordsVal s₀.mem B da i * Bv % M ∧
    Keep (passRegs ++ ([.r4] : List Reg)) s₀ s
  have hJ0 : J 0 s₀ := by
    refine ⟨by rw [h6]; rfl, Outside.refl _ _ _ _, by rw [hz]; omega_arith, by rw [hz]; simp [wordsVal],
      Keep.refl _ _⟩
  refine wp_countdown (body := .seq round (.block [.subi .r4 .r4 1])) (cnt := .r4) (N := w)
    (by omega_arith) (by omega_arith) J (fun i hi s hJ hc => ?_) hJ0 h4 |>.mono
    fun s ⟨_, jout, jlt, jeq, jk⟩ => ⟨⟨jlt, jeq, jout⟩, jk⟩
  obtain ⟨j6, jout, jlt, jeq, jk⟩ := hJ
  have keep : ∀ r ∈ [Reg.r0, .r3, .r7, .r8, .r10], s.gpr r = s₀.gpr r := fun r hr =>
    jk.gpr r (by revert r hr; decide)
  have vM : wordsVal s.mem B dM w = M := jout.wordsVal (by omega_arith) (by omega_arith)
  have vB : wordsVal s.mem B dB w = Bv := jout.wordsVal (by omega_arith) (by omega_arith)
  have wM : word s.mem B dM = word s₀.mem B dM := jout.word (by omega_arith) (by omega_arith)
  have wa : word s.mem B (da + 8 * i) = word s₀.mem B (da + 8 * i) := jout.word (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (round_ok (hs.congr jk.wr) j6
    (by rw [keep .r8 (by decide), h8]) (by rw [keep .r7 (by decide), h7])
    (by rw [keep .r10 (by decide), h10]) (by rw [keep .r3 (by decide), h3])
    (by rw [keep .r0 (by decide), wM]; exact hinv)
    hw hw' (by omega_arith) hA hB hM dBA dMA (by rw [vM]; exact jlt) (by rw [vM, vB]; exact hb))
    fun s₁ ⟨⟨k6, kout, u, hu, keq⟩, k₁⟩ => ?_)
  refine WP.mono (subi_ok s₁ .r4 (by decide)) fun s₂ e => ?_
  subst e
  rw [vM, vB, wa] at keq
  have hM0 : 0 < M := by omega_arith
  refine ⟨⟨by gsimp; rw [k6, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_, ?_⟩, ?_⟩
  · gsimp; exact jout.trans kout
  · gsimp; exact round_lt keq jlt (s₀.mem.readW _ 64).isLt hb hu
  · gsimp
    rw [wordsVal_succ_top s₀.mem B da i, Nat.mul_succ, Nat.pow_add]
    exact round_step keq jeq
  · have k₂ : Keep [.r4] s₁ (s₁.write .r4 (s₁.gpr .r4 - BitVec.ofNat 64 1)) := Keep.write _ _ _
    exact jk.trans' ((k₁.mono (by decide)).trans' (k₂.mono (by decide)))
  · gsimp
    rw [k₁.gpr _ (by decide)]

end VG.Proof.Bignum.PPC64LE
