module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentMarker
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairTwos
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowBit
import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The native alignment marker is exactly 2^(v2(N) mod 64) -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentMarker
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentMarker

theorem code_ok {s : State} {base : Addr} {size src count N : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) (value : val32 s.mem base src (2 * count) = N) (positive : 0 < N) :
    WP isa (code src count) s fun t =>
      t.gpr .edx ++ t.gpr .eax = BitVec.twoPow 64 ((Spec.Rsa.splitTwos N).1 % 64) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.seq (WP.mono (LowPair.scan_twos scratch fit value positive) fun a ⟨selectedWord, M, K⟩ => ?_)
  refine WP.mono (LowBit.code_ok a) fun t ⟨marker, Mt, Kt⟩ => ?_
  obtain ⟨factor, odd⟩ := VG.Proof.Rsa.splitTwos_spec positive
  rw [Nat.mul_comm] at factor
  obtain ⟨_, bit, below⟩ := VG.Proof.RsaKeyGen.lowWord_bits factor odd
  have setBit : (a.gpr .esi ++ a.gpr .ebx).getLsbD ((Spec.Rsa.splitTwos N).1 % 64) = true := by
    change (a.gpr .esi ++ a.gpr .ebx).toNat.testBit _ = true
    rw [selectedWord]
    exact bit
  have clearBit (j : Nat) (lt : j < (Spec.Rsa.splitTwos N).1 % 64) :
      (a.gpr .esi ++ a.gpr .ebx).getLsbD j = false := by
    change (a.gpr .esi ++ a.gpr .ebx).toNat.testBit j = false
    rw [selectedWord]
    exact below j lt
  exact ⟨marker.trans (VG.Proof.RsaKeyGen.and_neg_eq_twoPow (Nat.mod_lt _ (by decide)) setBit clearBit),
    Mt.trans M, K.widen Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentMarker
