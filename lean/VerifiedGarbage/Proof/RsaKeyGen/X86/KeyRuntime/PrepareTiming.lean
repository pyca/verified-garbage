module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrepareExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimesPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LcmPublic

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Sorted factors and LCM feed only the public exponent into control flow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aOne aE kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

structure Preparation (B : Addr) (Z n k e : Nat) (s : State) : Prop where
  workspace : Ws s B Z n 32
  pBound : num s.mem B n aPa < 2 ^ (32 * k)
  qBound : num s.mem B n aQa < 2 ^ (32 * k)
  zero : num s.mem B n aZero = 0
  one : num s.mem B n aOne = 1
  exponent : val32 s.mem B kEv 2 = e
  loaded : num s.mem B n aE = e

def PreparationPair (B : Addr) (Z n k e : Nat) (s t : State) : Prop :=
  Preparation B Z n k e s ∧ Preparation B Z n k e t ∧ VG.X86.Taint.Agree runtimeTaint s t

theorem prepareLoaded_trace (B : Addr) (Z n k e : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (PreparationPair B Z n k e) prepareLoaded
      (VG.X86.Taint.Agree runtimeTaint) := by
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
            public_trace (primes_public.seq lcm_public) _ _ _ _ _ _ agree leftPrefix rightPrefix
          obtain ⟨leftWs, leftE⟩ := wp_result
            (beforeExponent_ok Ps.workspace width positive even Ps.pBound Ps.qBound Ps.zero Ps.one) leftPrefix
          obtain ⟨rightWs, rightE⟩ := wp_result
            (beforeExponent_ok Pt.workspace width positive even Pt.pBound Pt.qBound Pt.zero Pt.one) rightPrefix
          obtain ⟨lastTrace, finalAgree⟩ := dSelect_trace B Z n e _ _ _ _ _ _
            ⟨leftWs, rightWs, prefixAgree, leftE.trans Ps.exponent, rightE.trans Pt.exponent⟩ Ad Cd
          refine ⟨?_, finalAgree⟩
          simp only [← List.append_assoc, prefixTrace, lastTrace]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
