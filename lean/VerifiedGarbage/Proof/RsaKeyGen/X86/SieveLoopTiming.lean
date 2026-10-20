module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStep
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStepTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The sieve leaks only the divisor pattern of a rejected candidate

Passing candidates have the all-false pattern, so their values remain secret.
Equal rejected candidates have the same pattern; the candidate contract can
therefore release the rejected candidate rather than impose a full-table pass.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Sieve

def SamePattern (g : Geometry) (c d : Nat) : Prop := ∀ i < g.limit, dividesAt c i = dividesAt d i

theorem loop_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d) :
    RelCT isa (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t)
      (loop stackSlots) (VG.X86.Taint.Agree (τr [.esp])) := by
  have raw : RelCT isa (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t)
      (.loop (step stackSlots) .ne) (VG.X86.Taint.Agree (τr [.esp])) := by
    refine (RelCT.loop (M := isa) (body := step stackSlots) (c := .ne)
      (I := fun q s t => ∃ i, i < g.limit ∧ q = g.limit - i ∧ StateAt g c i q s ∧ StateAt g d i q t)
      (Q := VG.X86.Taint.Agree (τr [.esp])) ?_ g.limit).mono
      (fun _ _ H => ⟨0, v.limitPositive, rfl, H⟩) (fun _ _ H => H)
    rintro q s t tr ur u z ⟨i, index, rfl, S, T⟩ E G
    have positive : 0 < g.limit - i := by omega
    have bound : g.limit - i < 2 ^ 32 := by have := v.limitBound; omega
    have hitEq := pattern i index
    have trace := (step_trace v (by have := v.limitBound; omega) _ _ _ _ _ _ ⟨S, T⟩ E G).1
    obtain ⟨U, _, Zu, _, _⟩ := wp_result (S.step v (by have := v.limitBound; omega) positive bound) E
    obtain ⟨Z, _, Zz, _, _⟩ := wp_result (T.step v (by have := v.limitBound; omega) positive bound) G
    rw [← hitEq] at Z Zz
    have nextBound : nextCount (g.limit - i) (dividesAt c i) < 2 ^ 32 := Nat.lt_trans (nextCount_lt positive _) bound
    have eu : isa.eval .ne u = some (!decide (nextCount (g.limit - i) (dividesAt c i) = 0)) := by
      change u.zf.map Bool.not = _
      rw [Zu, countWord_zero nextBound]
      rfl
    have ez : isa.eval .ne z = some (!decide (nextCount (g.limit - i) (dividesAt c i) = 0)) := by
      change z.zf.map Bool.not = _
      rw [Zz, countWord_zero nextBound]
      rfl
    refine ⟨trace, eu.trans ez.symm, ?_, ?_⟩
    · intro _
      exact agree_regs (by
        intro r mem
        obtain rfl := List.mem_singleton.mp mem
        exact U.context.stack.sp.trans Z.context.stack.sp.symm)
    · intro next
      have nz : nextCount (g.limit - i) (dividesAt c i) ≠ 0 := by
        intro zero
        rw [eu, decide_eq_true zero] at next
        cases next
      have missed : dividesAt c i = false := by
        by_cases hit : dividesAt c i = true
        · apply False.elim
          apply nz
          rw [hit]
          rfl
        · exact Bool.eq_false_iff.mpr hit
      have count : nextCount (g.limit - i) (dividesAt c i) = g.limit - (i + 1) := by
        rw [missed]
        change g.limit - i - 1 = g.limit - (i + 1)
        omega
      exact ⟨nextCount (g.limit - i) (dividesAt c i), nextCount_lt positive _, i + 1,
        by omega, count, U, Z⟩
  exact RelCT.seq raw (checkedBlockInvariant rfl rfl)

end VG.Proof.RsaKeyGen.X86.Sieve
