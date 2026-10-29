module

import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeValues
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMr
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMr

/-! # Public bookkeeping after normalization is fixed by the limb count -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.MillerRabin.X86_64 VG.Impl.Bignum

def normalizedPub (B : Addr) (Z w : Nat) (wr : List Region) : MrPub :=
  ⟨B, Z, w, wr, 0, 0, 0, 0, 0⟩

theorem normalized_mrh (m : Mem) (B : Addr) (Z w : Nat) (wr : List Region) :
    MrH (normalizedPub B Z w wr) 0 (8 * w) (normalizedMem m B w) := by
  have hv := normalized_values m B w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kOut (by simp [bookkeeping])
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kLen (by simp [bookkeeping])
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kUsedP (by simp [bookkeeping])
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kRand (by simp [bookkeeping])
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kRandLen (by simp [bookkeeping])
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kChecks (by simp [bookkeeping])
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kI (by simp [bookkeeping])
  · simpa [normalizedPub, kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, kE, kElen, sFn] using hv kUsed (by simp [bookkeeping])

theorem normalized_hp {s : State} {m : Mem} {B : Addr} {Z w : Nat} {wr : List Region}
    {mi : BitVec 64} (hg : Good s B Z w mi) (hw : s.wr = wr)
    (hm : s.mem = normalizedMem m B w) :
    HP B wr ((normalizedPub B Z w wr).vs 0 (8 * w)) s := by
  have hh : MrH (normalizedPub B Z w wr) 0 (8 * w) s.mem := by
    rw [hm]
    exact normalized_mrh m B Z w wr
  have hp := mr_hp (p := normalizedPub B Z w wr) (ex := []) hg hw hh (by simp)
  simpa only [List.append_nil, normalizedPub] using hp

end VG.Proof.MillerRabin.X86_64
