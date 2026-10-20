module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PackCT
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.Pack
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateCT

/-! # Final domain validation reads the public p, q, and g buffers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

def DomainBytesAt (P : SearchContextPlan) (bytes : List Byte) (s : State) : Prop :=
  SearchContextAt P s ∧
    Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen ++
    Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen ++
    Spec.Rsa.bytesAt s.mem (off P.geometry.base g) P.geometry.pLen = bytes

theorem finishDomain_ct (F : KeyRandom.CheckCall.CheckFn) (P : SearchContextPlan) (bytes : List Byte) :
    RelCT isa (Two fun (_ : Unit) => DomainBytesAt P bytes)
      (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (_ : Unit) => ValidateAt P bytes)
    ((pack_ct P).mono (fun _ _ => two_mono (fun _ _ h => h.1)) (fun _ _ h => h)) ?_)
    (validate_ct F P bytes)
  rintro _ s ⟨⟨W, R⟩, value⟩
  refine WP.mono (pack_ok R) fun t ⟨Rt, packed, _, _⟩ => ?_
  exact ⟨⟨W, Rt⟩, packed.trans value⟩
end VG.Proof.Dsa.X86.Generation
