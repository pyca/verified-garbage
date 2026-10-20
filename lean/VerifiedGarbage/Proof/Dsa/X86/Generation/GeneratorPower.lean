module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorPower
import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.Exponentiate

/-! # Generator exponentiation reuses the accepted candidate's Montgomery context -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem generatorPower_ok {n size p : Nat} {base : Addr} {s : State}
    (C : Context n p base size s) (width : n ≤ 48)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % p) :
    WP isa (generatorPower n) s fun t =>
      let value := wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p
      Context n p base size t ∧ wordsVal t.mem base (slot n 6) n = value ∧
      t.gpr .eax = (if 1 < value then 1 else 3) ∧
      Outs base (exponentRanges n (2 * n) ++ [(slot n 7, 8 * n)]) s.mem t.mem ∧ Keeps powerClob s t := by
  have positive : 0 < n := C.modulus.n0
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have := slot_bound (n := n) hj
    have := C.size_le
    unfold stride at *
    omega
  unfold generatorPower
  refine WP.seq (WP.mono (exponentiate_ok C (by omega) (Nat.le_refl _) (by omega) one r2)
    fun a ⟨Ca, value, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (lessThanConstant_ok Ca.scr positive (bounds 6 (by decide)) (bounds 7 (by decide))
    (by have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ 64 * n); omega)
    (.inl (by simp only [slot, stride]; omega))) fun b ⟨status, Kb, Ob⟩ => ?_)
  have Cb := Ca.outside_keep Kb (by decide) (by decide) Ob
    (.inl (by simp only [slot, stride]; omega)) (by simp only [slot, stride]; omega)
  have vb : wordsVal b.mem base (slot n 6) n =
      wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p := by
    rw [Ob.wordsVal (.inl (by simp only [slot, stride]; omega))
      (by have := Ca.scr.nowrap; have := bounds 6 (by decide); omega), value]
  have O : Outs base (exponentRanges n (2 * n) ++ [(slot n 7, 8 * n)]) s.mem b.mem :=
    (Oa.mono (fun _ hr => List.mem_append_left _ hr)).trans
      (Outs.of_outside Ob (by simp))
  have K := Ka.trans (Kb.mono (by decide))
  refine WP.seq (wp_cmpi fun c bc _ zc => WP.block_nil ?_)
  have z : c.zf = some (decide (1 < wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p)) := by
    rw [zc, status, value]
    by_cases h : wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p < 2
    · simp [mask32, h, show ¬ 1 < wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p by omega]
    · simp [mask32, h, show 1 < wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p by omega]
  have finish (t : State) (mem : t.mem = b.mem) (Kt : Keeps powerClob b t)
      (answer : t.gpr .eax = (if 1 < wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p then 1 else 3)) :
      Context n p base size t ∧ wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p ∧
      t.gpr .eax = (if 1 < wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p then 1 else 3) ∧
      Outs base (exponentRanges n (2 * n) ++ [(slot n 7, 8 * n)]) s.mem t.mem ∧ Keeps powerClob s t := by
    refine ⟨?_, by rw [mem]; exact vb, answer, by rw [mem]; exact O, K.trans Kt⟩
    refine ⟨Cb.scr.of_keeps Kt (by decide) (by decide), Cb.size_le, ?_, Cb.gt_one, ?_⟩
    · rw [mem]; exact Cb.modulus
    · rw [mem]; exact Cb.inverse
  by_cases good : 1 < wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) (2 * n) % p
  · refine WP.ite true (by simp [eval, z, good]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine wp_movS rfl fun t ct _ => WP.block_nil ?_
    exact finish t (ct.mem.trans bc.mem) ((bc.keeps _).trans (ct.keeps.mono (by decide))) (by rw [ct.gpr, ite_eq_left good])
  · refine WP.ite false (by simp [eval, z, good]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine wp_movS rfl fun t ct _ => WP.block_nil ?_
    exact finish t (ct.mem.trans bc.mem) ((bc.keeps _).trans (ct.keeps.mono (by decide))) (by rw [ct.gpr, ite_eq_right good])
end VG.Proof.Dsa.X86.Generation
