module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.Fios32
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Montgomery multiplication on PPC64LE: the rounds

A round (`round_ok`) replaces the accumulator `T` (`n + 1` digits) with `(T +
aᵢ b + u m) / 2³²`, for the digit `aᵢ` at the pointer `r6`, which it
advances; the `n` rounds (`rounds_ok`) leave `T < 2m` with `T 2^(32 n) ≡ a b
(mod m)`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE

/-- The registers a round writes. -/
def roundRegs : List Reg := [.r0, .r3, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

theorem round_ok {s : State} {B : Addr} {Z da dA dB dM n : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h8 : s.gpr .r8 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (h12 : (s.gpr .r12).toNat < 2 ^ 32) (hinv : (w32 s.mem B dM * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hn : 2 ≤ n) (hn' : n < 2 ^ 32)
    (ha : da + 4 ≤ Z) (hA : dA + 4 * (n + 1) ≤ Z) (hB : dB + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (dBA : dB + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dB) (dMA : dM + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dM) :
    WP isa round s fun s' =>
      (s'.gpr .r6 = off B (da + 4) ∧ Outside B dA (4 * (n + 1)) s.mem s'.mem ∧
        ∃ u < 2 ^ 32, 2 ^ 32 * val32 s'.mem B dA (n + 1) =
          val32 s.mem B dA (n + 1) + w32 s.mem B da * val32 s.mem B dB n + u * val32 s.mem B dM n) ∧
      Keep roundRegs s s' := by
  have hnw := hs.nowrap
  unfold round
  refine WP.seq (WP.mono (head_ok hs h6 h8 h7 h10 h11 h12 (by omega) (by omega) ha (by omega)
    (by omega) (by omega)) fun s₁ ⟨⟨i18, i6, i20, i19, i22, i14, i15, i16, i17, im⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have hmod : ((w32 s.mem B dA + w32 s.mem B da * w32 s.mem B dB) % 2 ^ 32 +
      (w32 s.mem B dA + w32 s.mem B da * w32 s.mem B dB) % 2 ^ 32 * (s.gpr .r12).toNat % 2 ^ 32 *
        w32 s.mem B dM) % 2 ^ 32 = 0 :=
    Fios32.mont_low _ _ _ hinv
  have hc1 : (s₁.gpr .r20).toNat < 2 ^ 32 := by
    rw [i20]; exact Fios32.mac_div_lt (b := w32 s.mem B dB) (d := 0) (s.mem.readW _ 32).isLt
      (s.mem.readW _ 32).isLt (s.mem.readW _ 32).isLt (by decide)
  have hc2 : (s₁.gpr .r22).toNat < 2 ^ 32 := by
    rw [i22]; exact Fios32.mac_div_lt (d := 0) (Nat.mod_lt _ (by decide)) (s.mem.readW _ 32).isLt
      (Nat.mod_lt _ (by decide)) (by decide)
  have hu : (s₁.gpr .r19).toNat < 2 ^ 32 := by rw [i19]; exact Nat.mod_lt _ (by decide)
  have h0 : w32 s₁.mem B dA + (s₁.gpr .r18).toNat * w32 s₁.mem B dB + (s₁.gpr .r19).toNat * w32 s₁.mem B dM =
      2 ^ 32 * ((s₁.gpr .r20).toNat + (s₁.gpr .r22).toNat) := by
    rw [im, i18, i19, i20, i22]
    have h1 := Nat.div_add_mod (w32 s.mem B dA + w32 s.mem B da * w32 s.mem B dB) (2 ^ 32)
    have h2 := Nat.div_add_mod ((w32 s.mem B dA + w32 s.mem B da * w32 s.mem B dB) % 2 ^ 32 +
      (w32 s.mem B dA + w32 s.mem B da * w32 s.mem B dB) % 2 ^ 32 * (s.gpr .r12).toNat % 2 ^ 32 *
        w32 s.mem B dM) (2 ^ 32)
    rw [hmod, Nat.add_zero] at h2
    rw [Nat.mul_add]
    omega
  refine WP.seq (WP.mono (inner_ok hs₁ i14 i15 i16 i17 hn (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [i18]; exact (s.mem.readW _ 32).isLt) hu hc1 hc2 h0)
    fun s₂ ⟨j14, j20, j22, jout, jeq, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  refine WP.mono (top_ok hs₂ j14 (by omega) j20 j22) fun s₃ ⟨jm, k₃⟩ => ?_
  have k23 := k₂.trans k₃
  refine ⟨⟨?_, ?_, (s₁.gpr .r19).toNat, hu, ?_⟩, ?_⟩
  · rw [k23.gpr _ (by decide), i6]
  · rw [jm, ← im]
    exact (jout.mono (Nat.le_refl _) (by omega)).trans
      (((writeW32_outside _ B (d := dA + 4 * (n - 1)) _ (by omega)).mono (by omega) (by omega)).trans
        ((writeW32_outside _ B (d := dA + 4 * (n - 1) + 4) _ (by omega)).mono (by omega) (by omega)))
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at jm jeq jout ⊢
    -- The top digit read is the one on entry.
    have wt : w32 s₂.mem B (dA + 4 * k + 4) = w32 s.mem B (dA + 4 * k + 4) := by
      rw [jout.w32 (by omega) (by omega), im]
    rw [jm, wt, val32_succ, (writeW32_outside _ B _ (by omega)).val32 (by omega) (by omega),
      show dA + 4 * (k + 1) = dA + 4 * k + 4 by omega, w32_write_self, BitVec.toNat_ofNat,
      val32_write_top _ _ _ _ _ (by omega), BitVec.toNat_ofNat]
    rw [im, i18] at jeq
    rw [val32_succ s.mem B dA (k + 1), show dA + 4 * (k + 1) = dA + 4 * k + 4 by omega]
    have htn : w32 s.mem B (dA + 4 * k + 4) < 2 ^ 32 := (s.mem.readW _ 32).isLt
    have := Fios32.top_eq (pow32_mul k) jeq htn j20 j22
    omega
  · exact ((k₁.trans k23).mono (by decide))

/-- The `n` rounds (`rounds`), counted by `r4` from `n`, over the digits of
`a` (at `da` of `B`, pointed to by `r6`), from the accumulator 0: `T < 2m`
and `T 2^(32 n) ≡ a b (mod m)`, for `b < m` (`n` digits each, at `dB` and
`dM`), only the accumulator's `n + 1` digits changed. -/
theorem rounds_ok {s₀ : State} {B : Addr} {Z da dA dB dM n : Nat} (hs : Scr s₀ B Z)
    (h6 : s₀.gpr .r6 = off B da) (h8 : s₀.gpr .r8 = off B dA) (h7 : s₀.gpr .r7 = off B dB)
    (h10 : s₀.gpr .r10 = off B dM) (h11 : s₀.gpr .r11 = BitVec.ofNat 64 n)
    (h4 : s₀.gpr .r4 = BitVec.ofNat 64 n)
    (h12 : (s₀.gpr .r12).toNat < 2 ^ 32) (hinv : (w32 s₀.mem B dM * (s₀.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hn : 2 ≤ n) (hn' : n < 2 ^ 32)
    (ha : da + 4 * n ≤ Z) (hA : dA + 4 * (n + 1) ≤ Z) (hB : dB + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (daA : da + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ da)
    (dBA : dB + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dB) (dMA : dM + 4 * n ≤ dA ∨ dA + 4 * (n + 1) ≤ dM)
    (hz : val32 s₀.mem B dA (n + 1) = 0) (hb : val32 s₀.mem B dB n < val32 s₀.mem B dM n) :
    WP isa rounds s₀ fun s =>
      (val32 s.mem B dA (n + 1) < 2 * val32 s₀.mem B dM n ∧
        2 ^ (32 * n) * val32 s.mem B dA (n + 1) % val32 s₀.mem B dM n =
          val32 s₀.mem B da n * val32 s₀.mem B dB n % val32 s₀.mem B dM n ∧
        Outside B dA (4 * (n + 1)) s₀.mem s.mem) ∧ Keep (roundRegs ++ ([.r4] : List Reg)) s₀ s := by
  have hnw := hs.nowrap
  let M := val32 s₀.mem B dM n
  let Bv := val32 s₀.mem B dB n
  let J : Nat → State → Prop := fun i s =>
    s.gpr .r6 = off B (da + 4 * i) ∧ Outside B dA (4 * (n + 1)) s₀.mem s.mem ∧
    val32 s.mem B dA (n + 1) < 2 * M ∧
    2 ^ (32 * i) * val32 s.mem B dA (n + 1) % M = val32 s₀.mem B da i * Bv % M ∧
    Keep (roundRegs ++ ([.r4] : List Reg)) s₀ s
  have hJ0 : J 0 s₀ := by
    refine ⟨by rw [h6]; rfl, Outside.refl _ _ _ _, by rw [hz]; omega, by rw [hz]; simp [val32], Keep.refl _ _⟩
  refine wp_countdown (body := .seq round (.block [.subi .r4 .r4 1])) (cnt := .r4) (N := n)
    (by omega) (by omega) J (fun i hi s hJ hc => ?_) hJ0 h4 |>.mono
    fun s ⟨_, jout, jlt, jeq, jk⟩ => ⟨⟨jlt, jeq, jout⟩, jk⟩
  obtain ⟨j6, jout, jlt, jeq, jk⟩ := hJ
  have keep : ∀ r ∈ [Reg.r7, .r8, .r10, .r11, .r12], s.gpr r = s₀.gpr r := fun r hr =>
    jk.gpr r (by revert r hr; decide)
  have wM : ∀ i < n, w32 s.mem B (dM + 4 * i) = w32 s₀.mem B (dM + 4 * i) := fun i hi =>
    jout.w32 (by omega) (by omega)
  have vM : val32 s.mem B dM n = M := jout.val32 (by omega) (by omega)
  have vB : val32 s.mem B dB n = Bv := jout.val32 (by omega) (by omega)
  have wa : w32 s.mem B (da + 4 * i) = w32 s₀.mem B (da + 4 * i) := jout.w32 (by omega) (by omega)
  refine WP.seq (WP.mono (round_ok (hs.congr jk.wr) j6
    (by rw [keep .r8 (by decide), h8]) (by rw [keep .r7 (by decide), h7])
    (by rw [keep .r10 (by decide), h10]) (by rw [keep .r11 (by decide), h11])
    (by rw [keep .r12 (by decide)]; exact h12)
    (by rw [keep .r12 (by decide), show dM = dM + 4 * 0 by rfl, wM 0 (by omega)]; exact hinv)
    hn hn' (by omega) hA hB hM dBA dMA) fun s₁ ⟨⟨k6, kout, u, hu, keq⟩, k₁⟩ => ?_)
  refine WP.mono (subi_ok s₁ .r4 (by decide)) fun s₂ e => ?_
  subst e
  rw [vM, vB, wa] at keq
  have hM0 : 0 < M := by omega
  refine ⟨⟨by gsimp; rw [k6, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_, ?_⟩, ?_⟩
  · gsimp; exact jout.trans kout
  · gsimp; exact Fios32.round_lt keq jlt (s₀.mem.readW _ 32).isLt hb hu
  · gsimp
    rw [val32_succ s₀.mem B da i, ← pow32_mul i, Nat.mul_comm (2 ^ 32) (2 ^ (32 * i))]
    exact Fios32.round_step keq jeq
  · have k₂ : Keep [.r4] s₁ (s₁.write .r4 (s₁.gpr .r4 - BitVec.ofNat 64 1)) :=
      ⟨fun r hr => by
        simp only [gpr_write]
        exact ite_eq_right_iff.mpr fun h => absurd h fun h => hr (by simp [h]), rfl, rfl, rfl, rfl⟩
    exact jk.trans' ((k₁.mono (by decide)).trans' (k₂.mono (by decide)))
  · gsimp
    rw [k₁.gpr _ (by decide)]

end VG.Proof.Bignum.PPC64LE
