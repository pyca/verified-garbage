module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyReady
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Public
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Prepare
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DOddTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DEvenTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DOnePublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ScalarKey
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyPrepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Primes
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LcmFrame
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Lcm
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.PrimesPublic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LcmTiming
/-! # Two secret factor pairs reach the retry comparison with the same public state -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/DSelectTiming.lean`, which only this module imported.
section

/-! # Public exponent branches compose with secret native arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key (kEv aE equalExponent parityExponent)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

structure ExponentPair (B : Addr) (Z n e : Nat) (s t : State) : Prop where
  left : Ws s B Z n 32
  right : Ws t B Z n 32
  agree : VG.X86.Taint.Agree runtimeTaint s t
  exponentLeft : val32 s.mem B kEv 2 = e
  exponentRight : val32 t.mem B kEv 2 = e
  loadedLeft : num s.mem B n aE = e
  loadedRight : num t.mem B n aE = e

def ExponentTest (B : Addr) (Z n e : Nat) (bit : Bool) (s t : State) : Prop :=
  ExponentPair B Z n e s t ∧ isa.eval .e s = some bit ∧ isa.eval .e t = some bit

theorem equalExponent_trace (B : Addr) (Z n e : Nat) (value : BitVec 32) :
    RelCT isa (ExponentPair B Z n e) (.block (equalExponent value))
      (ExponentTest B Z n e (decide (e = value.toNat))) := by
  have checked : Public (.block (equalExponent value)) := by
    refine ⟨(VG.Taint.hintOf taint runtimeTaint (Code.erase (.block (equalExponent 0) : Prog isa))),
        runtimeTaint, ?_, rfl⟩
    exact (check_of_erase_eq (.block (equalExponent value)) (.block (equalExponent 0) : Prog isa) runtimeTaint
      (VG.Taint.hintOf taint runtimeTaint (Code.erase (.block (equalExponent 0) : Prog isa))) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)).trans (by kernel_rfl)
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace checked _ _ _ _ _ _ P.agree A C
  obtain ⟨hu, Mu, flagU, _⟩ := wp_result (equalExponent_ok P.left value) A
  obtain ⟨hv, Mv, flagV, _⟩ := wp_result (equalExponent_ok P.right value) C
  rw [P.exponentLeft] at flagU
  rw [P.exponentRight] at flagV
  exact ⟨trace, ⟨hu, hv, agree, by rw [Mu]; exact P.exponentLeft,
    by rw [Mv]; exact P.exponentRight, by rw [Mu]; exact P.loadedLeft, by rw [Mv]; exact P.loadedRight⟩,
    flagU, flagV⟩

theorem parityExponent_trace (B : Addr) (Z n e : Nat) :
    RelCT isa (ExponentPair B Z n e) (.block parityExponent)
      (ExponentTest B Z n e (decide (e % 2 = 0))) := by
  have checked : Public (.block parityExponent) := ⟨.block [], runtimeTaint, rfl, rfl⟩
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace checked _ _ _ _ _ _ P.agree A C
  obtain ⟨hu, Mu, flagU, _⟩ := wp_result (parityExponent_ok P.left) A
  obtain ⟨hv, Mv, flagV, _⟩ := wp_result (parityExponent_ok P.right) C
  rw [P.exponentLeft] at flagU
  rw [P.exponentRight] at flagV
  exact ⟨trace, ⟨hu, hv, agree, by rw [Mu]; exact P.exponentLeft,
    by rw [Mv]; exact P.exponentRight, by rw [Mu]; exact P.loadedLeft, by rw [Mv]; exact P.loadedRight⟩,
    flagU, flagV⟩

/-- A public branch on the exponent, each side related when it is the one taken. -/
theorem exponent_branch_trace {B : Addr} {Z n e : Nat} {bit : Bool} {th el : Prog isa}
    (first : bit = true → RelCT isa (ExponentPair B Z n e) th (VG.X86.Taint.Agree runtimeTaint))
    (second : bit = false → RelCT isa (ExponentPair B Z n e) el (VG.X86.Taint.Agree runtimeTaint)) :
    RelCT isa (ExponentTest B Z n e bit) (.ite .e th el) (VG.X86.Taint.Agree runtimeTaint) := by
  apply RelCT.ite (fun _ _ P => P.2.1.trans P.2.2.symm)
  · intro s t tr ur u v P
    have taken : bit = true := by
      have := P.1.2.1.symm.trans P.2
      simpa using this
    exact first taken s t tr ur u v P.1.1
  · intro s t tr ur u v P
    have taken : bit = false := by
      have := P.1.2.1.symm.trans P.2
      simpa using this
    exact second taken s t tr ur u v P.1.1

theorem dSelect_trace (B : Addr) (Z n e : Nat) :
    RelCT isa (ExponentPair B Z n e) dSelect (VG.X86.Taint.Agree runtimeTaint) := by
  have even := (dEven_trace B Z n).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => ⟨P.left, P.right, P.agree⟩) (fun _ _ P => P)
  have one := (public_trace dOne_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  have zero := (public_trace dZero_public).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) => P.agree) (fun _ _ P => P)
  unfold dSelect
  refine RelCT.seq (equalExponent_trace B Z n e 0) (exponent_branch_trace (fun _ => zero) fun e0 => ?_)
  refine RelCT.seq (equalExponent_trace B Z n e 1) (exponent_branch_trace (fun _ => one) fun e1 => ?_)
  refine RelCT.seq (parityExponent_trace B Z n e) (exponent_branch_trace (fun _ => even) fun eo => ?_)
  have ne0 : e ≠ 0 := by simpa using e0
  have ne1 : e ≠ 1 := by simpa using e1
  have odd : e % 2 = 1 := by simp at eo; omega
  exact (dOdd_trace B Z n e (by omega) odd).mono
    (fun _ _ (P : ExponentPair B Z n e _ _) =>
      ⟨⟨P.left, P.exponentLeft, P.loadedLeft⟩, ⟨P.right, P.exponentRight, P.loadedRight⟩, P.agree⟩)
    (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/PrepareExponent.lean`, which only this module imported.
section

/-! # Factor preparation retains the imported public exponent before branching -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aOne aE kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (stageRanges prepareArrays stage_keep stage_mono stage_preserves_e
  stage_preserves_num)

theorem beforeExponent_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (boundP : num s.mem B n aPa < 2 ^ (32 * k)) (boundQ : num s.mem B n aQa < 2 ^ (32 * k))
    (zero : num s.mem B n aZero = 0) (one : num s.mem B n aOne = 1) :
    WP isa (.seq primes lcmPart) s fun t =>
      Ws t B Z n 32 ∧ val32 t.mem B kEv 2 = val32 s.mem B kEv 2 ∧ num t.mem B n aE = num s.mem B n aE := by
  have small : k ≤ n := by omega
  have pBound : max (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) := Nat.max_lt.mpr ⟨boundP, boundQ⟩
  have qBound : min (num s.mem B n aPa) (num s.mem B n aQa) < 2 ^ (32 * k) :=
    Nat.lt_of_le_of_lt (Nat.min_le_left ..) boundP
  refine WP.seq (WP.mono (primes_ok h width positive even boundP boundQ zero one)
    fun u ⟨hu, Ou, _, _, Pm, Qm, product, Ku⟩ => ?_)
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by decide) (h.fit64 (by decide))).trans one
  have frameU : Outs B (stageRanges n prepareArrays) s.mem u.mem :=
    stage_keep (Nat.le_refl n) (by simp only [eq_self, true_and]; decide) (by decide) Ou
  refine WP.mono (lcmPart_ok hu width positive
    (by rw [Pm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) pBound)
    (by rw [Qm]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) qBound) product oneU)
    fun t ⟨ht, Ot, _, _⟩ => ?_
  have spU : u.gpr .esp = s.gpr .esp := Ku.1 .esp (by decide)
  have frameT : OutsS B (s.gpr .esp) (stageRanges n prepareArrays) u.mem t.mem := by
    rw [← spU]
    exact OutsS.lift (fun _ _ O => stage_mono (by decide) (lcm_stage_frame small O)) Ot
  exact ⟨ht, h.read_val32 (by decide) ((OutsS.of_outs frameU).trans frameT) stage_preserves_e,
    h.read_num (by decide) ((OutsS.of_outs frameU).trans frameT)
      (stage_preserves_num (by decide) (by decide) (h.fit64 (by decide)))⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/PrepareTiming.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

structure CoreStart (B : Addr) (Z n k e p q : Nat) (s : State) : Prop extends Preparation B Z n k e s where
  pValue : num s.mem B n aPa = p
  qValue : num s.mem B n aQa = q

structure ReadyPair (B : Addr) (Z n e p q p' q' : Nat) (s t : State) : Prop where
  left : Ws s B Z n 32
  right : Ws t B Z n 32
  agree : VG.X86.Taint.Agree runtimeTaint s t
  leftReady : KeyReady B n e p q s.mem
  rightReady : KeyReady B n e p' q' t.mem

theorem prepareReady_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree runtimeTaint s t)
      prepareLoaded (ReadyPair B Z n e p q p' q') := by
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

end VG.Proof.RsaKeyGen.X86.KeyRuntime
