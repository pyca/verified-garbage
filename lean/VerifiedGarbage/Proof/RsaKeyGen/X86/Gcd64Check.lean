module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Check
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Body
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Setup
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Result
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete native 64-bit coprimality check, including precise scratch writes -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Gcd64

def checkRanges : List (Nat × Nat) := [(160, 24)] ++ ranges 2 arrays slots

theorem check_ok {s : State} {base : Addr} {size offset : Nat}
    (scratch : Scr s base size) (space : 400 ≤ size) (fit : offset + 8 ≤ size)
    (apart : offset + 8 ≤ 160 ∨ 168 ≤ offset) (odd : Mod64.exponentValue s.mem base offset % 2 = 1) :
    WP isa (check offset) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (Mod64.pair (s.gpr .ecx) (s.gpr .ebx))
        (Mod64.exponentValue s.mem base offset) = 1)).toNat ∧
      Outs base checkRanges s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  refine WP.seq (WP.mono (setup_ok scratch space fit apart) fun a ⟨Wa, R, E, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (code_ok Wa (by decide) (by rw [E]; exact odd)) fun b ⟨Wb, F, Kb, V⟩ => ?_)
  refine WP.mono (result_ok Wb.workspace (by omega)) fun t ⟨test, M, Kt⟩ => ?_
  rw [R, E] at V
  change t.gpr .eax = BitVec.ofNat 32 (decide (num b.mem base 2 1 = 1)).toNat at test
  rw [V] at test
  refine ⟨test, ?_, (((Ka.mono (by decide)).trans Kb).widen Kt)⟩
  rw [M]
  exact (Outs.of_outside Oa (List.mem_append_left _ (List.mem_singleton_self _))).trans
    (Outs.mono F (fun _ mem => List.mem_append_right _ mem))

end VG.Proof.RsaKeyGen.X86.Gcd64
