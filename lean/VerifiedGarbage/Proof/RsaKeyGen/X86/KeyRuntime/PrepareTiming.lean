module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrepareExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimesPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LcmTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Primes

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Sorted factors and LCM feed only the public exponent into control flow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aOne aE kEv aPm aQm aPhi)
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

theorem beforeExponent_trace (B : Addr) (Z n k e : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (PreparationPair B Z n k e) (.seq primes lcmPart) (VG.X86.Taint.Agree runtimeTaint) := by
  refine RelCT.seq (step_trace (Q := LcmStart B Z n k) primes_public fun s P =>
    WP.mono (primes_ok P.workspace width positive even P.pBound P.qBound P.zero P.one)
      fun u ⟨hu, _, _, _, Pm, Qm, product, _⟩ => ?_) (lcm_trace B Z n k width positive)
  refine ⟨hu, ?_, ?_, product⟩
  · rw [Pm]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.max_lt.mpr ⟨P.pBound, P.qBound⟩)
  · rw [Qm]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt (Nat.min_le_left ..) P.pBound)

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
            beforeExponent_trace B Z n k e width positive even _ _ _ _ _ _ ⟨Ps, Pt, agree⟩ leftPrefix rightPrefix
          obtain ⟨leftWs, leftE, leftL⟩ := wp_result
            (beforeExponent_ok Ps.workspace width positive even Ps.pBound Ps.qBound Ps.zero Ps.one) leftPrefix
          obtain ⟨rightWs, rightE, rightL⟩ := wp_result
            (beforeExponent_ok Pt.workspace width positive even Pt.pBound Pt.qBound Pt.zero Pt.one) rightPrefix
          obtain ⟨lastTrace, finalAgree⟩ := dSelect_trace B Z n e _ _ _ _ _ _
            ⟨leftWs, rightWs, prefixAgree, leftE.trans Ps.exponent, rightE.trans Pt.exponent,
              leftL.trans Ps.loaded, rightL.trans Pt.loaded⟩ Ad Cd
          refine ⟨?_, finalAgree⟩
          simp only [← List.append_assoc, prefixTrace, lastTrace]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
