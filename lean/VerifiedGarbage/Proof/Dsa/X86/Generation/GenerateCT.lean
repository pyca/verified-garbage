module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.InitializeSearchCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterCTState
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.InitializeSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.NativeParameterCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.NativeParameterSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterOutputCT

/-! # The initialized parameter generator has a trace determined by public inputs -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def GenerateAt (plen qlen : Nat) (P : SearchContextPlan) (s : State) : Prop :=
  StorageAt plen P s ∧ P.geometry.qLen = qlen

def SearchAt (plen qlen : Nat) (P : SearchContextPlan) (s : State) : Prop :=
  (∃ W, SearchContext P W s ∧ W 16 = 0) ∧ P.geometry.pLen = plen ∧ P.geometry.qLen = qlen

def searchPublicStart (P : SearchContextPlan) : ParameterPublic := ⟨P, 0, 0, Nat.zero_le _, Nat.zero_le _⟩

theorem generate_ct {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (plen qlen : Nat) (digest : H.D = qlen) (final : H.F = qlen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * qlen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * qlen) bs).length = qlen) :
    RelCT isa (Two (GenerateAt plen qlen)) (generate H F.name F.code plen qlen) (fun _ _ => True) := by
  unfold generate
  refine RelCT.seq (two_post (Ψ := SearchAt plen qlen)
    ((initializeSearch_ct plen).mono (fun _ _ => two_mono (fun _ _ h => h.1)) (fun _ _ h => h)) ?_)
    (RelCT.seq (two_post (Ψ := ParameterFinalAt)
      (two_map searchPublicStart (fun _ _ h => h) (nativeParameterSearch_ct K F plen qlen digest final hash hashSize)) ?_)
      parameterOutput_ct)
  · rintro P s ⟨⟨⟨W, R, cursor⟩, pl⟩, ql⟩
    rw [← pl]
    exact WP.mono (initializeSearch_ok R) fun t ⟨Rt, _, _⟩ => ⟨⟨W, Rt, cursor⟩, rfl, ql⟩
  · rintro P s ⟨⟨W, R, cursor⟩, pl, ql⟩
    rw [← pl, ← ql]
    exact WP.mono (nativeParameterSearch_ok K F R cursor (Nat.zero_le _)
      (digest.trans ql.symm) (final.trans ql.symm) (by simpa only [ql] using hash) (by simpa only [ql] using hashSize))
      fun _ result => ⟨s, result⟩
end VG.Proof.Dsa.X86.Generation
