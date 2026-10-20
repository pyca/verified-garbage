module

import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoop
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialFinish
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A whole-word i686 sieve pass returns the exact divisibility bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaKeyGen.X86.Trial

theorem divisor_ok (s : State) (p : BitVec 32) (w endOffset : Nat)
    (positive : 0 < w) (lengthBound : 4 * (2 * w) < 2 ^ 32) (fit : p.toNat + 4 * (2 * w) ≤ 2 ^ 32)
    (candidateRead : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off (byteAddr p) (4 * i)) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = p + BitVec.ofNat 32 (4 * (2 * w)))
    (ptr : s.gpr .edi = p) (zero : s.gpr .ebp = 0)
    (primeLow : 3 ≤ (s.gpr .ebx).toNat) (primeHigh : (s.gpr .ebx).toNat ≤ 8161)
    (odd : (s.gpr .ebx).toNat % 2 = 1)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (divisor endOffset) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (val32 s.mem (byteAddr p) 0 (2 * w) % (s.gpr .ebx).toNat = 0)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp, .edi] s t := by
  unfold divisor
  refine WP.seq (WP.mono (words_ok s p (2 * w) endOffset (by omega) lengthBound fit
    candidateRead endRead endValue ptr zero primeLow primeHigh inverse) fun a ⟨mem, K, bound, value⟩ => ?_)
  have prime : a.gpr .ebx = s.gpr .ebx := K.1 .ebx (by decide)
  have div : val32 s.mem (byteAddr p) 0 (2 * w) % (s.gpr .ebx).toNat = 0 ↔
      (a.gpr .ebp).toNat = 0 ∨ (a.gpr .ebp).toNat = (s.gpr .ebx).toNat := by
    apply VG.Proof.RsaKeyGen.trial_div odd bound
    rw [show 64 * w = 32 * (2 * w) by omega]
    exact value
  refine WP.mono (finish_ok (by rw [prime]; omega : 0 < (a.gpr .ebx).toNat)) fun t ⟨result, lastMem, lastK⟩ => ?_
  refine ⟨?_, lastMem.trans mem, K.widen lastK⟩
  rw [result, prime]
  simp only [← div]

end VG.Proof.RsaKeyGen.X86.Trial
