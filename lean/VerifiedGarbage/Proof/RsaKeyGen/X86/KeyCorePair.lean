module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrimesCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmFrame
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrimesTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmTiming
/-! # Two secret factor pairs reach the retry comparison with the same public state -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyPrepareExponent.lean`, which only this module imported.
section

/-! # Factor preparation retains the imported public exponent before branching -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem beforeExponent_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa (.seq (primes n) (lcmPart n)) s fun t =>
      Ws t B Z n 32 ∧ val32 t.mem B kEv 2 = val32 s.mem B kEv 2 := by
  have small : k ≤ n := by omega
  have pBound : max (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  have qBound : min (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) :=
    Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  refine WP.seq (WP.mono (primes_ok h width positive even boundP boundQ zero one)
    fun u ⟨hu, Ou, _, _, Pm, Qm, product, _⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  have frameU : Outs B (stageRanges n prepareArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  refine WP.mono (lcmPart_ok hu width positive
    (by rw [Pm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound) product oneU)
    fun t ⟨ht, Ot, _, _⟩ => ?_
  have frameT : Outs B (stageRanges n prepareArrays) u.mem t.mem :=
    stage_mono (by decide) (lcm_stage_frame small Ot)
  exact ⟨ht, stage_preserves_e (frameU.trans frameT)⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyPrepareTiming.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key

structure CoreStart (B : Addr) (Z n k e p q : Nat) (s : State) : Prop extends Preparation B Z n k e s where
  pValue : num s.mem B n aPa = p
  qValue : num s.mem B n aQa = q

structure ReadyPair (B : Addr) (Z n e p q p' q' : Nat) (s t : State) : Prop where
  left : Ws s B Z n 32
  right : Ws t B Z n 32
  agree : VG.X86.Taint.Agree (workspaceTaint true) s t
  leftReady : KeyReady B n e p q s.mem
  rightReady : KeyReady B n e p' q' t.mem

theorem prepareReady_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree (workspaceTaint true) s t)
      (prepareLoaded n) (ReadyPair B Z n e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨Ps, Pt, agree⟩ := P
  obtain ⟨trace, finalAgree⟩ := prepareLoaded_trace B Z n k e width positive even
    _ _ _ _ _ _ ⟨Ps.toPreparation, Pt.toPreparation, agree⟩ A C
  obtain ⟨leftWs, _, leftReady, _⟩ := wp_result
    (prepareLoaded_ok Ps.workspace width positive even Ps.pBound Ps.qBound Ps.zero Ps.one
      (Ps.loaded.trans Ps.exponent.symm)) A
  obtain ⟨rightWs, _, rightReady, _⟩ := wp_result
    (prepareLoaded_ok Pt.workspace width positive even Pt.pBound Pt.qBound Pt.zero Pt.one
      (Pt.loaded.trans Pt.exponent.symm)) C
  rw [Ps.exponent, Ps.pValue, Ps.qValue] at leftReady
  rw [Pt.exponent, Pt.pValue, Pt.qValue] at rightReady
  exact ⟨trace, leftWs, rightWs, finalAgree, leftReady, rightReady⟩

end VG.Proof.RsaKeyGen.X86.Key
