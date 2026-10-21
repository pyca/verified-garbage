module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrimesCorrect
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLcmFrame
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Factor preparation retains the imported public exponent before branching -/

@[expose] public section
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
