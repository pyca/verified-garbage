module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Draw
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA sampling on PPC64LE: up to 128 draws

`sample_ok`: `sample`, from the octets `u` of the tape on, is
`Random.sample q 128` on the tape from `u`: it leaves its status in `r31`,
`u` plus the octets it consumed in `r25`, and an accepted candidate in the
nonce's last `W` octets; it changes memory there only.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Spec.Dsa.Random (sample)
open VG.Proof.Dsa.Random (sampleStatus)

theorem sampleStatus_le (S : Spec.Dsa.Random.Sample) : sampleStatus S ≤ 2 := by
  unfold sampleStatus
  split
  · decide
  · split <;> decide

theorem status_sub4 : ∀ st < 3, (BitVec.ofNat 64 st - BitVec.ofNat 64 4 == 0) = false := by decide

/-- What `sample` leaves, for `S = Random.sample q 128` from `u`. -/
structure SampleOut (E : SE) (R : List Byte) (u : Nat) (S : Spec.Dsa.Random.Sample) (s t : State) : Prop where
  env : SEnv E R t
  out : Outside E.F E.o E.W s.mem t.mem
  keep : Keep drawRegs s t
  r31 : t.gpr .r31 = BitVec.ofNat 64 (sampleStatus S)
  r25 : t.gpr .r25 = BitVec.ofNat 64 (u + S.used)
  cand : ∀ k, S.scalar = some k → Spec.Dsa.decodeBE (cands E t.mem) = k

theorem sampleLoop_ok {E : SE} {qb R : List Byte} {s₀ : State} {u₀ : Nat} {S₀ : Spec.Dsa.Random.Sample}
    (hE : E.Ok) (hQ : E.Q qb) :
    ∀ d s u, 1 ≤ d → d ≤ 128 → SEnv E R s → s.gpr .r25 = BitVec.ofNat 64 u → u ≤ E.rl →
      s.gpr .r17 = BitVec.ofNat 64 d → s.gpr .r31 = BitVec.ofNat 64 4 →
      Outside E.F E.o E.W s₀.mem s.mem → Keep drawRegs s₀ s →
      (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = S₀.scalar →
      sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u)) = sampleStatus S₀ →
      u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used = u₀ + S₀.used →
      WP isa (.loop (.seq draw (.block [.subi .r3 .r31 4])) (.zero .d .r3)) s (SampleOut E R u₀ S₀ s₀) := by
  intro d₀ s₁ u₁ hd₀ hd₀' h₀ h₀25 hu₀ h₀17 h₀31 ho₀ hk₀ hsc₀ hst₀ hus₀
  refine WP.loop (M := isa) (fun n (t : State) => ∃ d u, n = d ∧ 1 ≤ d ∧ d ≤ 128 ∧ SEnv E R t ∧ t.gpr .r25 = BitVec.ofNat 64 u ∧
      u ≤ E.rl ∧ t.gpr .r17 = BitVec.ofNat 64 d ∧ t.gpr .r31 = BitVec.ofNat 64 4 ∧
      Outside E.F E.o E.W s₀.mem t.mem ∧ Keep drawRegs s₀ t ∧
      (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = S₀.scalar ∧
      sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u)) = sampleStatus S₀ ∧
      u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used = u₀ + S₀.used) ?_ d₀ s₁
    ⟨d₀, u₁, rfl, hd₀, hd₀', h₀, h₀25, hu₀, h₀17, h₀31, ho₀, hk₀, hsc₀, hst₀, hus₀⟩
  rintro n t ⟨_, u, rfl, hd, hd', h, h25, hu, h17, h31, ho, hk, hsc, hst, hus⟩
  refine WP.seq (WP.mono (draw_ok hE hQ h h25 hu h17 hd hd' h31) fun t₁ ⟨h1, o1, k1, hc⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .r3 = t₁.gpr .r31 - BitVec.ofNat 64 4) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_
  have h2 : SEnv E R t₂ := h1.step hE k2 (o := 0) (n := 0) (by omega) (by rw [m2]; exact Outside.refl _ _ _ _)
  have o2 : Outside E.F E.o E.W s₀.mem t₂.mem := by rw [m2]; exact ho.trans o1
  have k02 : Keep drawRegs s₀ t₂ := ((hk.trans k1).trans k2).mono (by decide)
  rcases hc with ⟨b31, h2d, b17, b25, hu', hrej⟩ | ⟨b31, b25, bc, -⟩
  · refine .inr ⟨?_, n - 1, by omega, n - 1, u + E.W, rfl, by omega, by omega, h2,
      (k2.gpr .r25 (by decide)).trans b25, hu', (k2.gpr .r17 (by decide)).trans b17,
      (k2.gpr .r31 (by decide)).trans b31, o2, k02, ?_, ?_, ?_⟩
    · rw [eval_zero, a3, b31]; rfl
    · rw [← hsc, hrej]
    · rw [← hst, hrej, Dsa.Random.sampleStatus_reject]
    · rw [← hus, hrej]; dsimp only; omega
  · refine .inl ⟨?_, ⟨h2, o2, k02, ?_, ?_, ?_⟩⟩
    · rw [eval_zero, a3, b31, status_sub4 _ (by have := sampleStatus_le (sample (Spec.Dsa.decodeBE qb) n (R.drop u)); omega)]
    · rw [(k2.gpr .r31 (by decide)).trans b31, hst]
    · rw [(k2.gpr .r25 (by decide)).trans b25, hus]
    · intro k hk'
      rw [m2]
      exact bc k (hsc.trans hk')

/-- `sample`: up to 128 draws from `u`. -/
theorem sample_ok {E : SE} {qb R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) :
    WP isa Impl.Dsa.PPC64LE.Random.sample s (SampleOut E R u (sample (Spec.Dsa.decodeBE qb) 128 (R.drop u)) s) := by
  unfold Impl.Dsa.PPC64LE.Random.sample
  refine WP.seq (WP.mono (WP.keep [.r17, .r31] (Q := fun t => t.mem = s.mem ∧
    t.gpr .r17 = BitVec.ofNat 64 128 ∧ t.gpr .r31 = BitVec.ofNat 64 4) (by prun) (by decide))
    fun t ⟨⟨tm, t17, t31⟩, k⟩ => ?_)
  exact sampleLoop_ok hE hQ 128 t u (by decide) (by decide)
    (h.step hE k (o := 0) (n := 0) (by omega) (by rw [tm]; exact Outside.refl _ _ _ _))
    ((k.gpr .r25 (by decide)).trans h25) hu t17 t31 (by rw [tm]; exact Outside.refl _ _ _ _) (k.mono (by decide))
    rfl rfl rfl

end VG.Proof.Dsa.PPC64LE.Rnd
