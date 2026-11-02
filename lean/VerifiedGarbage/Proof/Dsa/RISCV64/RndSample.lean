module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndDraw
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA sampling on RISC-V: the sampling loop

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Sample.lean`). `sample_ok`: up to
128 draws from the tape at `used`, against `Random.sample q 128`: the status
in `s10` is its status, the octets consumed in `s5`, and an accepted scalar
is the nonce's last `W` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
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
  s10 : t.gpr .s10 = BitVec.ofNat 64 (sampleStatus S)
  s5 : t.gpr .s5 = BitVec.ofNat 64 (u + S.used)
  cand : ∀ k, S.scalar = some k → Spec.Dsa.decodeBE (cands E t.mem) = k

theorem sampleLoop_ok {E : SE} {qb R : List Byte} {s₀ : State} {u₀ : Nat} {S₀ : Spec.Dsa.Random.Sample}
    (hE : E.Ok) (hQ : E.Q qb) :
    ∀ d s u, 1 ≤ d → d ≤ 128 → SEnv E R s → s.gpr .s5 = BitVec.ofNat 64 u → u ≤ E.rl →
      s.gpr .s11 = BitVec.ofNat 64 d → s.gpr .s10 = BitVec.ofNat 64 4 →
      Outside E.F E.o E.W s₀.mem s.mem → Keep drawRegs s₀ s →
      (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = S₀.scalar →
      sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u)) = sampleStatus S₀ →
      u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used = u₀ + S₀.used →
      WP isa (.loop (.seq draw (.block [.addi .a0 .s10 (-4)])) (.zero .a0)) s (SampleOut E R u₀ S₀ s₀) := by
  intro d₀ s₁ u₁ hd₀ hd₀' h₀ h₀25 hu₀ h₀17 h₀31 ho₀ hk₀ hsc₀ hst₀ hus₀
  refine WP.loop (M := isa) (fun n (t : State) => ∃ d u, n = d ∧ 1 ≤ d ∧ d ≤ 128 ∧ SEnv E R t ∧
      t.gpr .s5 = BitVec.ofNat 64 u ∧
      u ≤ E.rl ∧ t.gpr .s11 = BitVec.ofNat 64 d ∧ t.gpr .s10 = BitVec.ofNat 64 4 ∧
      Outside E.F E.o E.W s₀.mem t.mem ∧ Keep drawRegs s₀ t ∧
      (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).scalar = S₀.scalar ∧
      sampleStatus (sample (Spec.Dsa.decodeBE qb) d (R.drop u)) = sampleStatus S₀ ∧
      u + (sample (Spec.Dsa.decodeBE qb) d (R.drop u)).used = u₀ + S₀.used) ?_ d₀ s₁
    ⟨d₀, u₁, rfl, hd₀, hd₀', h₀, h₀25, hu₀, h₀17, h₀31, ho₀, hk₀, hsc₀, hst₀, hus₀⟩
  rintro n t ⟨_, u, rfl, hd, hd', h, h25, hu, h17, h31, ho, hk, hsc, hst, hus⟩
  refine WP.seq (WP.mono (draw_ok hE hQ h h25 hu h17 hd hd' h31) fun t₁ ⟨h1, o1, k1, hc⟩ => ?_)
  refine WP.mono (wp_sp (WP.keep [.a0] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .a0 = t₁.gpr .s10 - BitVec.ofNat 64 4) (by brun) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨m2, a3⟩, k2⟩, sp2⟩ => ?_
  have h2 : SEnv E R t₂ := h1.stepM hE k2 sp2 m2
  have o2 : Outside E.F E.o E.W s₀.mem t₂.mem := by rw [m2]; exact ho.trans o1
  have k02 : Keep drawRegs s₀ t₂ := ((hk.trans k1).trans k2).mono (by decide)
  rcases hc with ⟨b31, h2d, b17, b25, hu', hrej⟩ | ⟨b31, b25, bc, -⟩
  · refine .inr ⟨?_, n - 1, by omega, n - 1, u + E.W, rfl, by omega, by omega, h2,
      (k2.gpr (by decide)).trans b25, hu', (k2.gpr (by decide)).trans b17,
      (k2.gpr (by decide)).trans b31, o2, k02, ?_, ?_, ?_⟩
    · rw [Steps.eval_zero, a3, b31]; rfl
    · rw [← hsc, hrej]
    · rw [← hst, hrej, Dsa.Random.sampleStatus_reject]
    · rw [← hus, hrej]; dsimp only; omega
  · refine .inl ⟨?_, ⟨h2, o2, k02, ?_, ?_, ?_⟩⟩
    · rw [Steps.eval_zero, a3, b31,
        status_sub4 _ (by have := sampleStatus_le (sample (Spec.Dsa.decodeBE qb) n (R.drop u)); omega)]
    · rw [(k2.gpr (by decide)).trans b31, hst]
    · rw [(k2.gpr (by decide)).trans b25, hus]
    · intro k hk'
      rw [m2]
      exact bc k (hsc.trans hk')

/-- `sample`: up to 128 draws from `u`. -/
theorem sample_ok {E : SE} {qb R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (hQ : E.Q qb)
    (h : SEnv E R s) (h5 : s.gpr .s5 = BitVec.ofNat 64 u) (hu : u ≤ E.rl) :
    WP isa Impl.Dsa.RISCV64.Random.sample s (SampleOut E R u (sample (Spec.Dsa.decodeBE qb) 128 (R.drop u)) s) := by
  unfold Impl.Dsa.RISCV64.Random.sample
  refine WP.seq (WP.mono (wp_sp (WP.keep [.s11, .s10] (Q := fun t => t.mem = s.mem ∧
    t.gpr .s11 = BitVec.ofNat 64 128 ∧ t.gpr .s10 = BitVec.ofNat 64 4)
    (by brun [exec_li_lit (show 128 < 2048 by decide), exec_li_lit (show 4 < 2048 by decide)]) (by decide) (by rfl)))
    fun t ⟨⟨⟨tm, t17, t31⟩, k⟩, spt⟩ => ?_)
  exact sampleLoop_ok hE hQ 128 t u (by decide) (by decide) (h.stepM hE k spt tm)
    ((k.gpr (by decide)).trans h5) hu t17 t31 (by rw [tm]; exact Outside.refl _ _ _ _) (k.mono (by decide))
    rfl rfl rfl

end VG.Proof.Dsa.RISCV64.Rnd
