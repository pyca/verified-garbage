import VerifiedGarbage.Proof.MdStream.Arm.Update
import VerifiedGarbage.Proof.MdStream.Arm.Finalize
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Sm3.Md
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm3.Arm.Compress
import VerifiedGarbage.Impl.Sm3.Arm.Stream

/-!
# Streaming SM3 on ARMv7: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/Arm.lean`), so they are verified by the generic proofs
(`Proof/MdStream/Arm/`) for SM3's instance (`Proof/Sm3/Md.lean`), given what
SM3's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

namespace VG.Proof.Sm3.Arm.Stream

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm

abbrev params := Impl.Sm3.Arm.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hout := len64_ok (d := params.N + (params.B - params.L)) (be := true) (by decide)
    (by have : params.B = 64 := rfl; have : params.L = 8 := rfl; omega) hout
  out _ f₀ f₆ hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) f₀ f₆ hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨fun r h _ => g r h, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sm3.Arm.compress :=
  ⟨compress_verified.1, by lit_decide, by rw [← Code.allInstrs_eq]; lit_decide⟩

namespace Update

theorem update_verified : Verified Arm.target Impl.Sm3.Arm.Stream.update Proof.Sm3.updateArm :=
  have h := MdStream.Arm.Update.verified (name := "vg_sm3_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Update.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Update.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.Arm.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified Arm.target Impl.Sm3.Arm.Stream.finalize Proof.Sm3.finalizeArm :=
  have h := MdStream.Arm.Finalize.verified (name := "vg_sm3_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀ params)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀ h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.Arm.Finalize.sat params

end Finalize

end VG.Proof.Sm3.Arm.Stream
