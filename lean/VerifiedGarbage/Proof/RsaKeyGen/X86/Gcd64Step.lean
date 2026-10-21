module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.RsaKeyGen.Gcd
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.InvU

/-! # Reuse the verified native inverse's u/v step as a 64-bit binary GCD step -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem bankStep_ok {s : State} {base : Addr} {size count a b : Nat}
    (W : Ws s base size 2 count) (space : 15 ≤ count) (bank : (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0)) :
    WP isa (bankStep a b) s fun t =>
      Ws t base size 2 count ∧ Keep base 2 [b, b + 1, aT1, aT2, aT3] [sOdd, sB, sC] s.mem t.mem ∧
      (num t.mem base 2 b, num t.mem base 2 (b + 1)) =
        VG.Proof.RsaKeyGen.gcdStep (num s.mem base 2 a) (num s.mem base 2 (a + 1)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  refine WP.mono (invU_ok W space bank) fun t ⟨Wt, F, _, _, V, U, K⟩ => ?_
  refine ⟨Wt, F, ?_, K⟩
  rw [U, V]
  by_cases odd : num s.mem base 2 a % 2 = 1 <;>
    by_cases less : num s.mem base 2 a < num s.mem base 2 (a + 1) <;>
    simp [VG.Proof.RsaKeyGen.gcdStep, odd, less]

end VG.Proof.RsaKeyGen.X86.Gcd64
