module

public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Proof.Mont.X86.Exponentiate
public import VerifiedGarbage.Proof.Dsa.X86.CorePowerFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! # Shared IA-32 DSA exponentiation: arithmetic and memory effects -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

theorem core_ok {s : State} {base : Addr} {size n e m : Nat}
    (hs : Scr s base size) (hz : contextBytes n ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (core n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      Outs base (setupRanges n ++ exponentRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have hnz : contextBytes n ≤ 2 ^ 64 := by omega
  unfold core
  refine WP.seq (WP.mono (contextSetup_ok hs hn (by omega) hz hv hm1 hodd)
    fun u ⟨Cu, One, R2, Ou, Ku⟩ => ?_)
  have A : wordsVal u.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply Ou.val32
    · simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]
      omega
    · simp only [contextBytes, slot, stride] at hnz ⊢
      omega
  have E : val32 u.mem base (slot n 8) e = val32 s.mem base (slot n 8) e := by
    apply Ou.val32
    · simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]
      omega
    · simp only [contextBytes, slot, stride] at hnz ⊢
      omega
  refine WP.mono (exponentiate_ok Cu he hen (by omega) One R2)
    fun t ⟨_, V, O, K⟩ => ⟨by rw [V, A, E], ?_, Ku.trans K⟩
  exact (Ou.mono (fun _ h => List.mem_append_left _ h)).trans
    (O.mono (fun _ h => List.mem_append_right _ h))

end VG.Proof.Dsa.X86.Pow
