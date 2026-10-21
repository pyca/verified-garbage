module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepareExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrimesTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Sorted factors and LCM feed only the public exponent into control flow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure Preparation (B : Addr) (Z n k e : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  pBound : num s.mem B n aPa < 2 ^ (32 * k)
  qBound : num s.mem B n aQa < 2 ^ (32 * k)
  zero : num s.mem B n aZero = 0
  one : num s.mem B n aOne = 1
  exponent : val32 s.mem B kEv 2 = e
  loaded : num s.mem B n aE = e

def PreparationPair (B : Addr) (Z n k e : Nat) (s t : State) : Prop :=
  Preparation B Z n k e s ∧ Preparation B Z n k e t ∧ VG.X86.Taint.Agree (workspaceTaint true) s t

theorem prepareLoaded_trace (B : Addr) (Z n k e : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (PreparationPair B Z n k e) (prepareLoaded n)
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur u v P A C
  obtain ⟨Ps, Pt, agree⟩ := P
  unfold prepareLoaded seqs at A C
  cases A with
  | seq Ap Ar =>
    cases Ar with
    | seq Al Ad =>
      cases C with
      | seq Cp Cr =>
        cases Cr with
        | seq Cl Cd =>
          have leftPrefix := Exec.seq Ap Al
          have rightPrefix := Exec.seq Cp Cl
          obtain ⟨prefixTrace, prefixAgree⟩ :=
            key_public_trace ((primes_public n).seq (lcmPart_public n)) _ _ _ _ _ _ agree leftPrefix rightPrefix
          obtain ⟨leftWs, leftE⟩ := wp_result
            (beforeExponent_ok Ps.workspace width positive even Ps.pBound Ps.qBound Ps.zero Ps.one) leftPrefix
          obtain ⟨rightWs, rightE⟩ := wp_result
            (beforeExponent_ok Pt.workspace width positive even Pt.pBound Pt.qBound Pt.zero Pt.one) rightPrefix
          obtain ⟨lastTrace, finalAgree⟩ := dSelect_trace B Z n e _ _ _ _ _ _
            ⟨leftWs, rightWs, prefixAgree, leftE.trans Ps.exponent, rightE.trans Pt.exponent⟩ Ad Cd
          refine ⟨?_, finalAgree⟩
          simp only [← List.append_assoc, prefixTrace, lastTrace]

end VG.Proof.RsaKeyGen.X86.Key
