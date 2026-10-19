module

public import VerifiedGarbage.Proof.MdStream.X86.Finalize
meta import VerifiedGarbage.Proof.MdStream.X86.Finalize
public import VerifiedGarbage.Proof.MdStream.X86.Update
meta import VerifiedGarbage.Proof.MdStream.X86.Update
import VerifiedGarbage.Proof.MdStream.X86.Words
meta import VerifiedGarbage.Proof.MdStream.X86.Words
public import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.Sm3.Md
public import VerifiedGarbage.Proof.Sm3.X86.Contract
meta import VerifiedGarbage.Proof.Sm3.X86.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm3.X86.Compress
meta import VerifiedGarbage.Proof.Sm3.X86.Compress
import VerifiedGarbage.Impl.Sm3.X86.Stream
meta import VerifiedGarbage.Impl.Sm3.X86.Stream
public import VerifiedGarbage.Proof.Sm3.X86.Lit
meta import VerifiedGarbage.Proof.Sm3.X86.Lit
public import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Streaming SM3 on x86 (32-bit): `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for SM3's instance (`Proof/Sm3/Md.lean`) with 160
bytes of scratch space, given what SM3's own pieces do: its length field and
digest (`shape`), that its compression function is verified (`callee`), and
that the taint analysis accepts its code (which it checks together with the
compression function's).
-/

@[expose] public section

namespace VG.Proof.Sm3.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev params := Impl.Sm3.X86.Stream.params

theorem dims : Dims params 160 := ⟨.inl rfl, by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hlo hhi ho := len64_ok (so := params.so) (d := params.N + params.B - params.L) (be := true)
    (by have : params.N + params.B - params.L + 8 = params.N + params.B := rfl; omega) hlo hhi
    (ho _ (Nat.le_refl _) (by decide)) (ho _ (by decide) (by decide))
  out _ hbx hax hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hbx hax hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ =>
      ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sm3.X86.compress :=
  ⟨compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Sm3.X86.Stream.update Proof.Sm3.updateX86 :=
  have h := MdStream.X86.Update.verified (name := "vg_sm3_compress") dims callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Update.τ₀ params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat params 160

end Update

namespace Finalize

theorem finalize_verified : Verified X86.target Impl.Sm3.X86.Stream.finalize Proof.Sm3.finalizeX86 :=
  have h := MdStream.X86.Finalize.verified (name := "vg_sm3_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Finalize.τ₀ params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide))
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86.Finalize.sat params 160

end Finalize

end VG.Proof.Sm3.X86.Stream
