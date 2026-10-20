module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MillerRabinMath
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundEffects
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundControl

/-! # A public primality-test step either decides the result or consumes one square -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem roundStep_ok {base : Addr} {n m size k : Nat} {s : State} (R : RoundReady base n m size s)
    (hk : 1 ≤ k) (bound : k < 2 ^ 32) (count : s.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 k) :
    WP isa (roundStep n) s fun t =>
      let z := wordsVal s.mem base (slot n 6) n
      let z' := z * z % m
      wordsVal t.mem base (slot n 6) n = z' ∧
      t.zf = some (decide (z' = 1 ∨ z' = m - 1 ∨ k = 1)) ∧ RoundReady base n m size t ∧
      Outs base (roundWrites n) s.mem t.mem ∧ Keeps clob s t ∧
      ((t.zf = some true ∧ t.mem.readW (off base roundStatus) 32 =
        mask32 (publicMrSquares m k (wordsVal s.mem base (slot n 6) n) = true)) ∨
       (t.zf = some false ∧ 1 < k ∧ t.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 (k - 1) ∧
        publicMrSquares m k (wordsVal s.mem base (slot n 6) n) =
          publicMrSquares m (k - 1) (wordsVal t.mem base (slot n 6) n))) := by
  let z := wordsVal s.mem base (slot n 6) n
  let z' := z * z % m
  have ksucc : k = (k - 1) + 1 := by omega
  unfold roundStep
  refine WP.seq (WP.mono (roundSquare_ok R) fun a ⟨Ra, zf, status, value, ca, Oa, Ka⟩ => ?_)
  change a.zf = some (decide (¬ (z' = 1 ∨ z' = m - 1))) at zf
  change a.mem.readW (off base roundStatus) 32 = mask32 (z' = m - 1) at status
  change wordsVal a.mem base (slot n 6) n = z' at value
  by_cases terminal : z' = 1 ∨ z' = m - 1
  · refine WP.ite true (by simp [eval, zf, terminal]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.mono roundStop_ok fun t ⟨zt, mem, K⟩ => ?_
    refine ⟨by rw [mem]; exact value, by change t.zf = some (decide (z' = 1 ∨ z' = m - 1 ∨ k = 1)); simp only [← or_assoc, terminal, true_or, decide_true, zt], Ra.unchanged mem K (by decide) (by decide), by rw [mem]; exact Oa, Ka.trans K, .inl ⟨zt, ?_⟩⟩
    rw [mem, status]
    change mask32 (z' = m - 1) = mask32 (publicMrSquares m k z = true)
    rw [ksucc, publicMrSquares]
    by_cases minus : z' = m - 1
    · simp only [show (z * z % m == m - 1) = true by exact beq_iff_eq.mpr minus, ite_true]
      simp [mask32, minus]
    · have one : z' = 1 := terminal.resolve_right minus
      simp only [show (z * z % m == m - 1) = false by exact beq_eq_false_iff_ne.mpr minus,
        Bool.false_eq_true, ite_false, show (z * z % m == 1) = true by exact beq_iff_eq.mpr one, ite_true]
      simp [mask32, minus]
  · refine WP.ite false (by simp [eval, zf, terminal]) (fun e => Bool.noConfusion e) (fun _ => ?_)
    refine WP.mono (roundNext_ok Ra hk bound (ca.trans count)) fun t ⟨Rt, ct, zt, O, K⟩ => ?_
    have vt : wordsVal t.mem base (slot n 6) n = z' := by
      rw [wordsVal_eq_val32]
      have same := O.val32 (d := slot n 6) (k := 2 * n)
        (by have := Ra.bound (j := 6) (by decide); omega)
        (by have := Ra.bound (j := 6) (by decide); unfold roundCount at *; omega)
      rw [same, ← wordsVal_eq_val32, value]
    have st : t.mem.readW (off base roundStatus) 32 = 0 := by
      have same : t.mem.readW (off base roundStatus) 32 = a.mem.readW (off base roundStatus) 32 := by
        apply BitVec.eq_of_toNat_eq
        exact O.w32 (by decide) (by decide)
      rw [same, status]
      simp [mask32, show z' ≠ m - 1 from fun h => terminal (.inr h)]
    have recurrence : publicMrSquares m k z = publicMrSquares m (k - 1) z' := by
      rw [ksucc, publicMrSquares]
      simp only [show (z * z % m == m - 1) = false by exact beq_eq_false_iff_ne.mpr (fun h => terminal (.inr h)),
        show (z * z % m == 1) = false by exact beq_eq_false_iff_ne.mpr (fun h => terminal (.inl h)), Bool.false_eq_true, ite_false, Nat.add_sub_cancel]
      rfl
    refine ⟨vt, by change t.zf = some (decide (z' = 1 ∨ z' = m - 1 ∨ k = 1)); simpa only [← or_assoc, terminal, false_or] using zt, Rt, Oa.trans (roundWrites_control O (.inl rfl)), Ka.trans K, ?_⟩
    by_cases last : k = 1
    · refine .inl ⟨by simpa only [last, decide_true] using zt, ?_⟩
      rw [st, recurrence, last]
      rfl
    · exact .inr ⟨by simpa only [last, decide_false] using zt, by omega, ct, by rw [vt]; exact recurrence⟩
end VG.Proof.Dsa.X86.Generation
