module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialPointer
import VerifiedGarbage.Proof.RsaKeyGen.Trial32
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialWord
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Words
/-! # A whole-word i686 sieve pass returns the exact divisibility bit -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/TrialLoop.lean`, which only this module imported.
section

/-! # Reduce every candidate word while preserving its modular prefix invariant -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/TrialFinishMath.lean`, which only this module imported.
section

/-! # Convert the bounded Montgomery residue into a divisibility bit -/

section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG

theorem word_zero (x : BitVec 32) : decide (x.toNat < (1 : BitVec 32).toNat) = decide (x = 0#32) := by
  apply decide_eq_decide.mpr
  rw [← BitVec.toNat_inj]
  change x.toNat < 1 ↔ x.toNat = 0
  omega

theorem sub_zero (a b : BitVec 32) : a - b = 0#32 ↔ a = b := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem finish_bits (a b : BitVec 32) (positive : 0 < b.toNat) :
    ((0#32 + 0 + carryWord (decide (a.toNat < (1 : BitVec 32).toNat))) + 0 +
      carryWord (decide ((a - b).toNat < (1 : BitVec 32).toNat))) =
      BitVec.ofNat 32 (decide (a.toNat = 0 ∨ a.toNat = b.toNat)).toNat := by
  rw [word_zero, word_zero]
  have zeroIff : a.toNat = 0 ↔ a = 0#32 := by rw [← BitVec.toNat_inj]; rfl
  have eqIff : a.toNat = b.toNat ↔ a = b := BitVec.toNat_inj
  simp only [sub_zero, zeroIff, eqIff]
  by_cases zero : a = 0#32
  · have different : a ≠ b := by intro eq; rw [← eq, zero] at positive; contradiction
    rw [decide_eq_true zero, decide_eq_false different, decide_eq_true (Or.inl zero)]
    rfl
  · by_cases same : a = b
    · rw [decide_eq_false zero, decide_eq_true same, decide_eq_true (Or.inr same)]
      rfl
    · rw [decide_eq_false zero, decide_eq_false same, decide_eq_false (not_or_intro zero same)]
      rfl

end VG.Proof.RsaKeyGen.X86.Trial
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/TrialFinish.lean`, which only this module imported.
section

/-! # Execute the branch-free small-prime divisibility test -/

section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Trial

theorem finish_ok {s : State} (positive : 0 < (s.gpr .ebx).toNat) :
    WP isa (.block finish) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide ((s.gpr .ebp).toNat = 0 ∨ (s.gpr .ebp).toNat = (s.gpr .ebx).toNat)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold finish
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => wp_subS rfl fun c C cf => ?_
  refine wp_adcS rfl cf fun d D _ => wp_subS rfl fun e E _ => wp_subS rfl fun f F cfF => ?_
  refine wp_adcS rfl cfF fun t T _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [T.gpr, F.other .eax (by decide), E.other .eax (by decide), D.gpr,
      C.other .eax (by decide), B.other .eax (by decide), A.gpr,
      B.gpr, A.other .ebp (by decide),
      E.gpr, D.other .ebp (by decide), C.other .ebp (by decide), B.other .ebp (by decide),
      A.other .ebp (by decide), D.other .ebx (by decide), C.other .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
    exact finish_bits _ _ positive
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
  · exact ((((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen F.keeps).widen T.keeps

end VG.Proof.RsaKeyGen.X86.Trial
end

end

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
    (primeLow : 3 ≤ (s.gpr .ebx).toNat) (primeHigh : (s.gpr .ebx).toNat ≤ 65537)
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
