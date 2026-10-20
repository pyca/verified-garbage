module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TestWitness
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.X86.WidthConstant

/-! # The native witness classifier matches RSA's uniform interval -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem testWitness_ok {s : State} {base : Addr} {size n : Nat} (S : Scr s base size)
    (hn : 0 < n) (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size) :
    WP isa (testWitness n) s fun t =>
      let good := 2 ≤ wordsVal s.mem base (slot n 5) n ∧ wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 8) n
      t.mem.readW (off base primeIsUniform) 32 = mask32 good ∧ t.zf = some (decide (¬good)) ∧
      Outs base [(slot n 7, 8 * n), (primeIsUniform, 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have bounds (j : Nat) (hj : j ≤ 8) : slot n j + 8 * n ≤ size := by
    have mul := Nat.mul_le_mul_right (16 * n + 8) hj
    simp only [slot, stride, primeIsUniform] at *
    omega
  unfold testWitness
  refine WP.seq (WP.mono (lessThan_ok n S hn (bounds 5 (by decide)) (bounds 8 (by decide))) fun a ⟨va, Ka, ma⟩ => ?_)
  refine WP.seq (wp_movS rfl fun b ab _ => WP.block_nil ?_)
  have Kb : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s b := (Ka.mono (by decide)).widen ab.keeps
  refine WP.seq (WP.mono (lessThanConstant_ok (S.of_keeps Kb (by decide)) hn
    (bounds 5 (by decide)) (bounds 7 (by decide))
    (by have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ 64 * n); omega)
    (by simp only [slot, stride]; omega)) fun c ⟨vc, Kc, Oc⟩ => ?_)
  unfold testWitnessFinish
  refine wp_logicS (.inr rfl) rfl fun d cd => wp_logicS (.inl rfl) rfl fun e de => ?_
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s e := ((Kb.trans (Kc.mono (by decide))).widen cd.keeps).widen de.keeps
  have se := S.of_keeps K (by decide)
  have value : e.gpr .eax = mask32 (2 ≤ wordsVal s.mem base (slot n 5) n ∧
      wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 8) n) := by
    rw [de.gpr, ite_eq_left rfl, cd.gpr, ite_eq_right (by decide), vc,
      cd.other _ (by decide), Kc.1 _ (by decide), ab.gpr, va, ab.mem, ma, mask_not]
    by_cases lo : wordsVal s.mem base (slot n 5) n < 2 <;>
      by_cases hi : wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 8) n <;>
      simp [mask32, lo, hi, show (2 ≤ wordsVal s.mem base (slot n 5) n) ↔ ¬ wordsVal s.mem base (slot n 5) n < 2 by omega]
  refine wp_storeS (se.ea (by omega)) (se.write room) fun f ef => wp_cmpi fun t ft _ zt => WP.block_nil ?_
  refine ⟨by rw [ft.mem, ef.mem, Mem.readW_writeW_self32, value], ?_, ?_, K.trans ((ef.keeps _).trans (ft.keeps _))⟩
  · rw [zt, ef.gpr, value]
    by_cases good : 2 ≤ wordsVal s.mem base (slot n 5) n ∧ wordsVal s.mem base (slot n 5) n < wordsVal s.mem base (slot n 8) n <;> simp [mask32, good]
  · have Oe : Outside base (slot n 7) (8 * n) s.mem e.mem := by rw [de.mem, cd.mem]; rw [ab.mem, ma] at Oc; exact Oc
    have Ot : Outside base primeIsUniform 4 e.mem t.mem := by
      rw [ft.mem, ef.mem]
      exact writeW32_outside _ _ _ (by have := S.nowrap; omega)
    exact (Outs.of_outside Oe (by simp)).trans (Outs.of_outside Ot (by simp))
end VG.Proof.Dsa.X86.Generation
