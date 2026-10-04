import VerifiedGarbage.Proof.Sha1.X86.Stream.Md

/-!
# Streaming SHA-1 parameterized by compression on x86

The functional and ABI proofs of `update` and `finalize` (`Md.lean`) hold once
for every verified compression function. Each implementation of the
compression function (`Proof/Sha1/X86/Variants/`) supplies constant-time
certificates for the streaming code made with it, checked against the same
streaming contracts.
-/
namespace VG.Proof.Sha1.X86.Stream

open VG.X86
open VG.Proof.MdStream VG.Proof.MdStream.X86

variable {name : String} {code : Prog isa}
  (hcomp : CalleeOk (P := params) md code)
include hcomp

/-- Any verified compression function gives the same SHA-1 `update` contract. -/
theorem update_of (ct : ConstantTime isa (updK (P := params) md 160).pre
    (updK (P := params) md 160).pub (Impl.MdStream.X86.update params name code)) :
    Verified X86.target (Impl.MdStream.X86.update params name code) Proof.Sha1.updateX86 :=
  Verified.of_implies (MdStream.X86.Update.verified (name := name) dims hcomp ct)
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc, fun _ _ _ _ h => h,
      (MdStream.X86.Update.verified (name := name) dims hcomp ct).2.2⟩

/-- Any verified compression function gives the same SHA-1 `finalize` contract. -/
theorem finalize_of (ct : ConstantTime isa (finK (P := params) md 160).pre
    (finK (P := params) md 160).pub (Impl.MdStream.X86.finalize params name code)) :
    Verified X86.target (Impl.MdStream.X86.finalize params name code) Proof.Sha1.finalizeX86 :=
  Verified.of_implies (MdStream.X86.Finalize.verified (name := name) dims shape hcomp ct)
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc, fun _ _ _ _ h => h,
      (MdStream.X86.Finalize.verified (name := name) dims shape hcomp ct).2.2⟩

end VG.Proof.Sha1.X86.Stream
