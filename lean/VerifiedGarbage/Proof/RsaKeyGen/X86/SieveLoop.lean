module

import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStep
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext

/-! # The early-exit loop is exactly trial division by the required prefix -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem loop_full_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State}
    (H : StateAt g c 0 g.limit s) :
    WP isa (loop stackSlots) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix c g.limit).toNat ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate := by
  let Inv : Nat → State → Prop := fun q t =>
    ∃ i, i < g.limit ∧ q = g.limit - i ∧ StateAt g c i q t ∧
      VG.Proof.RsaKeyGen.trialPrefix c i = false ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t
  have initial : Inv g.limit s :=
    ⟨0, v.limitPositive, rfl, H, rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have run : WP isa (.loop (step stackSlots) .ne) s fun t =>
      Context g c t ∧ t.mem.readW (off (g.sp.setWidth 64) 16) 32 =
        BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix c g.limit).toNat ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate := by
    refine WP.loop (M := isa) Inv ?_ g.limit s initial
    rintro q t ⟨i, index, rfl, T, clearPrefix, O, K⟩
    have positive : 0 < g.limit - i := by omega
    have bound : g.limit - i < 2 ^ 32 := by have := v.limitBound; omega
    refine WP.mono (T.step v (by have := v.limitBound; omega) positive bound)
      fun u ⟨U, hit, Z, Ou, Ku⟩ => ?_
    have nextBound : nextCount (g.limit - i) (dividesAt c i) < 2 ^ 32 :=
      Nat.lt_trans (nextCount_lt positive _) bound
    have ev : isa.eval .ne u = some (!decide (nextCount (g.limit - i) (dividesAt c i) = 0)) := by
      change u.zf.map Bool.not = _
      rw [Z, countWord_zero nextBound]
      rfl
    have combinedO := O.trans Ou
    have combinedK := K.trans Ku
    by_cases found : dividesAt c i = true
    · have countZero : nextCount (g.limit - i) (dividesAt c i) = 0 := by rw [found]; rfl
      have full : VG.Proof.RsaKeyGen.trialPrefix c g.limit = true :=
        VG.Proof.RsaKeyGen.trialPrefix_hit index found
      refine Or.inl ⟨by rw [ev, countZero]; rfl, U.context, ?_, combinedO, combinedK, U.candidate⟩
      rw [full]
      rw [found] at hit
      exact hit
    · have missed : dividesAt c i = false := Bool.eq_false_iff.mpr found
      have nextPrefix : VG.Proof.RsaKeyGen.trialPrefix c (i + 1) = false := by
        rw [VG.Proof.RsaKeyGen.trialPrefix_succ, clearPrefix]
        exact missed
      have count : nextCount (g.limit - i) (dividesAt c i) = g.limit - (i + 1) := by
        rw [missed]
        unfold nextCount
        change g.limit - i - 1 = g.limit - (i + 1)
        omega
      by_cases done : i + 1 = g.limit
      · have countZero : nextCount (g.limit - i) (dividesAt c i) = 0 := by rw [count, done]; omega
        refine Or.inl ⟨by rw [ev, countZero]; rfl, U.context, ?_, combinedO, combinedK, U.candidate⟩
        rw [done] at nextPrefix
        rw [nextPrefix]
        rw [missed] at hit
        exact hit
      · have still : 0 < g.limit - (i + 1) := by omega
        refine Or.inr ⟨?_, g.limit - (i + 1), by omega, i + 1, by omega, rfl, ?_, nextPrefix, combinedO, combinedK⟩
        · rw [ev, count, decide_eq_false (by omega : ¬ g.limit - (i + 1) = 0)]
          rfl
        · rw [count] at U
          exact U
  unfold loop
  refine WP.seq (WP.mono run fun t ⟨C, value, O, K, candidate⟩ => ?_)
  refine wp_movS (C.stack.read 16 (by decide)) fun u U _ => WP.block_nil ?_
  refine ⟨U.gpr.trans value, ?_, K.widen U.keeps, ?_⟩
  · rw [U.mem]; exact O
  · rw [U.mem]; exact candidate

theorem loop_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State}
    (H : StateAt g c 0 g.limit s) :
    WP isa (loop stackSlots) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.RsaKeyGen.trialPrefix c g.limit).toNat ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t :=
  WP.mono (loop_full_ok v H) fun _ ⟨result, O, K, _⟩ => ⟨result, O, K⟩

end VG.Proof.RsaKeyGen.X86.Sieve
