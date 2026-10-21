module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Preserve
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Check
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Setup
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Result
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSave
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The general exponent check preserves a saved candidate and restores its original buffer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem ranges_below {r : Nat × Nat} (mem : r ∈ checkRanges) : r.1 + r.2 ≤ 400 := by
  simp only [checkRanges, ranges, arrays, slots, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem preserving_ok {s : State} {base : Addr} {size n dst saved offset : Nat}
    (scratch : Scr s base size) (space : 400 ≤ size) (fit : offset + 8 ≤ size)
    (apart : offset + 8 ≤ 160 ∨ 168 ≤ offset) (odd : Mod64.exponentValue s.mem base offset % 2 = 1)
    (positive : 0 < n) (dstFit : dst + 4 * n ≤ size) (savedFit : saved + 4 * n ≤ size)
    (dstLo : 256 ≤ dst) (savedLo : 400 ≤ saved) (sep : dst + 4 * n ≤ saved)
    (even : val32 s.mem base saved n % 2 = 0) :
    WP isa (preserving n dst saved offset) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (Mod64.pair (s.gpr .ecx) (s.gpr .ebx))
        (Mod64.exponentValue s.mem base offset) = 1)).toNat ∧
      val32 t.mem base dst n = val32 s.mem base saved n + 1 ∧
      Outs base (checkRanges ++ [(dst, 4 * n)]) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  refine WP.seq (WP.mono (setup_ok scratch space fit apart) fun a ⟨Wa, R, E, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (code_ok Wa (by decide) (by rw [E]; exact odd)) fun b ⟨Wb, F, Kb, V⟩ => ?_)
  have Ftotal : Outs base checkRanges s.mem b.mem :=
    (Outs.of_outside Oa (List.mem_append_left _ (List.mem_singleton_self _))).trans
      (Outs.mono F (fun _ mem => List.mem_append_right _ mem))
  have savedValue : val32 b.mem base saved n = val32 s.mem base saved n :=
    Ftotal.val32 (fun r mem => Or.inr (by have := ranges_below mem; omega))
      (by have := scratch.nowrap; omega)
  refine WP.seq (WP.mono (CandidateSave.restore_ok Wb.workspace positive savedFit dstFit
    (Or.inr (Or.inl sep)) (by rw [savedValue]; exact even)) fun c ⟨restored, Oc, Kc⟩ => ?_)
  refine WP.mono (result_ok (Wb.workspace.of_keeps Kc (by decide)) (by omega))
    fun t ⟨test, M, Kt⟩ => ?_
  have bank : num c.mem base 2 1 = num b.mem base 2 1 :=
    Oc.val32 (Or.inl (by change 176 + 4 * 2 ≤ dst; omega)) (by change 176 + 4 * 2 ≤ 2 ^ 64; decide)
  change t.gpr .eax = BitVec.ofNat 32 (decide (num c.mem base 2 1 = 1)).toNat at test
  rw [bank, V, R, E] at test
  refine ⟨test, ?_, ?_, ?_⟩
  · rw [M, restored, savedValue]
  · rw [M]
    exact (Ftotal.mono (fun _ mem => List.mem_append_left _ mem)).trans
      (Outs.of_outside Oc (List.mem_append_right _ (List.mem_singleton_self _)))
  · exact (((Ka.mono (by decide)).trans Kb).widen Kc).widen Kt

end VG.Proof.RsaKeyGen.X86.Gcd64
