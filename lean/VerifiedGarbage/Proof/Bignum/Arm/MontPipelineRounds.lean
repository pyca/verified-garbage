module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Lift any native scanning round through the existing Montgomery pipeline. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem rounds_ok (round : Prog isa) (law : RoundLaw round) (s : State) {base : BitVec 32} {size tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (even : n % 2 = 0) (hdr : RoundMeta s.mem base tmp a b mod acc n 0 inv)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (hzero : val32 s.mem (State.addr base) acc (n + 2) = 0)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.rounds round) s (MontInv s base tmp a b mod acc n n inv) := by
  have hn := ctx.count
  let loopInv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ MontInv s base tmp a b mod acc n i inv t
  unfold VG.Impl.Bignum.Arm.MontPipeline.rounds
  refine WP.loop (M := isa) loopInv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (loopBody_ok round law ctx even hi (by omega) hB hInv) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, by omega, ?_⟩
    refine ⟨by omega, hdr, ptr, ?_, ?_, Outs.refl _ _ _, Rest.refl _ _⟩
    · rw [hzero]
      simp only [val32, Nat.mul_zero, Nat.zero_mul, Nat.zero_mod]
    · rw [hzero]
      omega


theorem RoundLaw.loop {round : Prog isa} (law : RoundLaw round) : LoopLaw round :=
  fun s _ _ _ _ _ _ _ _ _ ctx even hdr ptr hzero hB hInv => rounds_ok round law s ctx even hdr ptr hzero hB hInv

end VG.Proof.Bignum.Arm.MontPipeline
