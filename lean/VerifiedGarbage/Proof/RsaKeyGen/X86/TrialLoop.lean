module

import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialPointer
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.RsaKeyGen.Trial32
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoad

/-! # Reduce every candidate word while preserving its modular prefix invariant -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaKeyGen.X86.Trial

def Prefix (s0 : State) (p : BitVec 32) (i : Nat) (s : State) : Prop :=
  s.mem = s0.mem ∧ Keeps [.eax, .edx, .ecx, .ebp, .edi] s0 s ∧
    s.gpr .edi = p + BitVec.ofNat 32 (4 * i) ∧
    (s.gpr .ebp).toNat < 2 * (s0.gpr .ebx).toNat ∧
    (s.gpr .ebp).toNat * 2 ^ (32 * i) % (s0.gpr .ebx).toNat =
      val32 s0.mem (byteAddr p) 0 i % (s0.gpr .ebx).toNat

theorem words_ok (s : State) (p : BitVec 32) (n endOffset : Nat)
    (positive : 0 < n) (lengthBound : 4 * n < 2 ^ 32) (fit : p.toNat + 4 * n ≤ 2 ^ 32)
    (candidateRead : ∀ i < n, InRegions (s.rd ++ s.wr) (off (byteAddr p) (4 * i)) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = p + BitVec.ofNat 32 (4 * n))
    (ptr : s.gpr .edi = p) (zero : s.gpr .ebp = 0)
    (primeLow : 3 ≤ (s.gpr .ebx).toNat) (primeHigh : (s.gpr .ebx).toNat ≤ 65537)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (words endOffset) s fun t => t.mem = s.mem ∧
      Keeps [.eax, .edx, .ecx, .ebp, .edi] s t ∧
      (t.gpr .ebp).toNat < 2 * (s.gpr .ebx).toNat ∧
      (t.gpr .ebp).toNat * 2 ^ (32 * n) % (s.gpr .ebx).toNat =
        val32 s.mem (byteAddr p) 0 n % (s.gpr .ebx).toNat := by
  have initial : Prefix s p 0 s := by
    refine ⟨rfl, Keeps.refl _ _, ?_, ?_, ?_⟩
    · simpa only [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using ptr
    · rw [zero]
      change 0 < _
      omega
    · rw [zero]
      simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_mod, val32]
  refine WP.loop (M := isa) (fun m t => ∃ i, m = n - i ∧ i < n ∧ Prefix s p i t)
    ?_ n s ⟨0, rfl, positive, initial⟩
  rintro m t ⟨i, rfl, index, M, K, ptrT, accBound, remainder⟩
  have ebxT := K.1 .ebx (by decide)
  have esiT := K.1 .esi (by decide)
  have espT := K.1 .esp (by decide)
  refine WP.mono (wordStep_ok t endOffset (p + BitVec.ofNat 32 (4 * n))
    (by rw [K.2.1, K.2.2, ptrT, word_address p fit index]; exact candidateRead i index)
    (by rw [K.2.1, K.2.2, espT]; exact endRead)
    (by rw [M, espT]; exact endValue)
    (by rw [ebxT]; exact primeLow) (by rw [ebxT]; exact primeHigh)
    (by rw [ebxT]; exact accBound) (by rw [ebxT, esiT]; exact inverse)) ?_
  rintro u ⟨Mu, Ku, ptrU, boundU, residueU, zfU⟩
  have nextPtr : u.gpr .edi = p + BitVec.ofNat 32 (4 * (i + 1)) := by
    rw [ptrU, ptrT, BitVec.add_assoc]
    change p + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add]
    congr 2 <;> omega
  have next : Prefix s p (i + 1) u := by
    refine ⟨Mu.trans M, K.trans Ku, nextPtr, ?_, ?_⟩
    · rw [ebxT] at boundU
      exact boundU
    · rw [ebxT, M, ptrT, word_address p fit index] at residueU
      have step := VG.Proof.RsaKeyGen.trial_word32 residueU remainder
      simpa only [val32_succ, Nat.zero_add] using step
  have ev : isa.eval .ne u = some (!decide (i + 1 = n)) := by
    rw [show isa.eval .ne u = u.zf.map (!·) from rfl, zfU, ptrT]
    have calcPtr : p + BitVec.ofNat 32 (4 * i) + 4 = p + BitVec.ofNat 32 (4 * (i + 1)) := by
      rw [BitVec.add_assoc]
      change p + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
      rw [← BitVec.ofNat_add]
      congr 2 <;> omega
    rw [calcPtr, pointer_zf p lengthBound index]
    rfl
  by_cases done : i + 1 = n
  · refine Or.inl ⟨by rw [ev, decide_eq_true done]; rfl, ?_⟩
    rw [done] at next
    exact ⟨next.1, next.2.1, next.2.2.2⟩
  · exact Or.inr ⟨by rw [ev, decide_eq_false done]; rfl, n - (i + 1), by omega,
      i + 1, rfl, by omega, next⟩

end VG.Proof.RsaKeyGen.X86.Trial
