import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Sha1.Scratch
import VerifiedGarbage.Proof.Sha1.X86.Compress
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Sha1.X86.Stream

/- Proofs formerly in `VerifiedGarbage.Proof.Sha1.X86.Stream.Md`. -/
section

/-!
# Streaming SHA-1 on x86 (32-bit): `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for SHA-1's instance (`Proof/Sha1/Md.lean`) with 160
bytes of scratch space, given what SHA-1's own pieces do: its length field and
digest (`shape`), that its compression function is verified (`callee`), and
that the taint analysis accepts its code (which it checks together with the
compression function's).
-/

namespace VG.Proof.Sha1.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev params := Impl.Sha1.X86.Stream.params

theorem dims : Dims VG.Proof.Sha1.X86.Stream.params 160 := ⟨.inl rfl, by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := VG.Proof.Sha1.X86.Stream.params) md where
  len _ hfit hlo hhi ho := len64_ok (so := params.so) (d := params.N + params.B - params.L) (be := true)
    (by have : params.N + params.B - params.L + 8 = params.N + params.B := rfl; omega) hlo hhi
    (ho _ (Nat.le_refl _) (by decide)) (ho _ (by decide) (by decide))
  out _ hbx hax hin hout hd := by
    refine (out32_ok (n := 5) true (by decide) hbx hax hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ =>
      ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := VG.Proof.Sha1.X86.Stream.params) md Impl.Sha1.X86.compress :=
  ⟨compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Sha1.X86.Stream.update Proof.Sha1.updateX86 :=
  have h := MdStream.X86.Update.verified (name := "vg_sha1_compress") VG.Proof.Sha1.X86.Stream.dims VG.Proof.Sha1.X86.Stream.callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Update.τ₀ VG.Proof.Sha1.X86.Stream.params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ VG.Proof.Sha1.X86.Stream.dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat VG.Proof.Sha1.X86.Stream.params 160

end Update

namespace Finalize

theorem finalize_verified : Verified X86.target Impl.Sha1.X86.Stream.finalize Proof.Sha1.finalizeX86 :=
  have h := MdStream.X86.Finalize.verified (name := "vg_sha1_compress") VG.Proof.Sha1.X86.Stream.dims VG.Proof.Sha1.X86.Stream.shape VG.Proof.Sha1.X86.Stream.callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Finalize.τ₀ VG.Proof.Sha1.X86.Stream.params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀ VG.Proof.Sha1.X86.Stream.dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86.Finalize.sat VG.Proof.Sha1.X86.Stream.params 160

end Finalize

end VG.Proof.Sha1.X86.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha1.X86.Stream.Variant`. -/
section

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
  (hcomp : CalleeOk (P := VG.Proof.Sha1.X86.Stream.params) md code)
include hcomp

/-- Any verified compression function gives the same SHA-1 `update` contract. -/
theorem update_of (ct : ConstantTime isa (updK (P := VG.Proof.Sha1.X86.Stream.params) md 160).pre
    (updK (P := VG.Proof.Sha1.X86.Stream.params) md 160).pub (Impl.MdStream.X86.update VG.Proof.Sha1.X86.Stream.params name code)) :
    Verified X86.target (Impl.MdStream.X86.update VG.Proof.Sha1.X86.Stream.params name code) Proof.Sha1.updateX86 :=
  Verified.of_implies (MdStream.X86.Update.verified (name := name) VG.Proof.Sha1.X86.Stream.dims hcomp ct)
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr hc, fun _ _ _ _ h => h,
      (MdStream.X86.Update.verified (name := name) VG.Proof.Sha1.X86.Stream.dims hcomp ct).2.2⟩

/-- Any verified compression function gives the same SHA-1 `finalize` contract. -/
theorem finalize_of (ct : ConstantTime isa (finK (P := VG.Proof.Sha1.X86.Stream.params) md 160).pre
    (finK (P := VG.Proof.Sha1.X86.Stream.params) md 160).pub (Impl.MdStream.X86.finalize VG.Proof.Sha1.X86.Stream.params name code)) :
    Verified X86.target (Impl.MdStream.X86.finalize VG.Proof.Sha1.X86.Stream.params name code) Proof.Sha1.finalizeX86 :=
  Verified.of_implies (MdStream.X86.Finalize.verified (name := name) VG.Proof.Sha1.X86.Stream.dims VG.Proof.Sha1.X86.Stream.shape hcomp ct)
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha1.H0 m hr trivial hc, fun _ _ _ _ h => h,
      (MdStream.X86.Finalize.verified (name := name) VG.Proof.Sha1.X86.Stream.dims VG.Proof.Sha1.X86.Stream.shape hcomp ct).2.2⟩

end VG.Proof.Sha1.X86.Stream

end
