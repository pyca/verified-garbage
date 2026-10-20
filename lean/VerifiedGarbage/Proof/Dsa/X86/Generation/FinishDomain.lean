module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.Pack
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites
import VerifiedGarbage.Proof.Dsa.X86.Generation.Validate
import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateResources

/-! # Pack and validate a candidate domain before the seed search returns success -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem finishDomain_ok (F : KeyRandom.CheckCall.CheckFn) {P : SearchContextPlan} {W : Nat → BitVec 32}
    {s : State} {params : Spec.Dsa.Params} (R : SearchContext P W s)
    (pb : Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen params.p)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen) = params.q)
    (gb : Spec.Rsa.bytesAt s.mem (off P.geometry.base g) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen params.g)
    (pBound : params.p < 256 ^ P.geometry.pLen) (qBound : params.q < 256 ^ P.geometry.qLen)
    (gBound : params.g < 256 ^ P.geometry.pLen) :
    WP isa (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen) s fun t =>
      SearchContext P (frameUpdate W 19 (if Spec.Dsa.parametersValid params then 1 else 3)) t ∧
      Spec.Rsa.bytesAt t.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) =
        Spec.Dsa.encodeParams P.geometry.pLen P.geometry.qLen params ∧
      Frame (parameterWrites P.geometry) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have pw := P.geometry.width
  have qw := P.geometry.qWidth
  have room := validate_packed_room P.geometry
  have qb : Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen = Spec.Dsa.encodeBE P.geometry.qLen params.q := by
    have h := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen)
    rw [qval] at h
    simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using h.symm
  unfold finishDomain
  refine WP.seq (WP.mono (pack_ok R) fun a ⟨Ra, bytes, Oa, Ka⟩ => ?_)
  rw [pb, qb, gb] at bytes
  change Spec.Rsa.bytesAt a.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) =
    Spec.Dsa.encodeParams P.geometry.pLen P.geometry.qLen params at bytes
  have result : validateResult P.geometry a.mem = decide (Spec.Dsa.parametersValid params) := by
    unfold validateResult
    rw [bytes]
    exact VG.Proof.Dsa.Generation.check_encodedParams (validate_lengths _) pBound qBound gBound
  refine WP.mono (validate_ok F Ra) fun t ⟨Rt, Ot, Kt⟩ => ?_
  rw [result] at Rt
  have preserved : Spec.Rsa.bytesAt t.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) =
      Spec.Rsa.bytesAt a.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) :=
    drawFrame_bytes Ot (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact validate_packedApart _ r hr
      · obtain rfl := List.mem_singleton.mp hr; exact (P.geometry.frame_part room).symm) (by omega)
  have first : Frame (parameterWrites P.geometry) s.mem a.mem := Oa.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, P.geometry.mutablePart (by decide) room⟩)
  have last : Frame (parameterWrites P.geometry) a.mem t.mem := Ot.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact validate_mutable _ r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [parameterWrites], fun _ h => h⟩)
  exact ⟨by simpa only [decide_eq_true_eq] using Rt, preserved.trans bytes, first.trans last,
    (Ka.mono (by decide)).trans Kt⟩
end VG.Proof.Dsa.X86.Generation
