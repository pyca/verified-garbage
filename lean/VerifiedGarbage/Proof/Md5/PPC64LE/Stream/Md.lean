module

public import VerifiedGarbage.Proof.MdStream.PPC64LE.Update
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Finalize
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
public import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Update
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Finalize
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
meta import VerifiedGarbage.Proof.Md5.Md
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
meta import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming MD5 on PPC64LE: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/PPC64LE.lean`), so they are verified by the generic proofs
(`Proof/MdStream/PPC64LE/`) for MD5's instance (`Proof/Md5/Md.lean`), given
what MD5's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

@[expose] public section

namespace VG.Proof.Md5.PPC64LE.Stream

open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE

abbrev params := Impl.Md5.PPC64LE.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : ShapeD (P := params) md 16 where
  le := by decide
  len _ hout := len64_ok (d := params.N + params.B - params.L) (be := false) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 4) false (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq, List.take_of_length_le (by simp only [List.length_flatMap, bytes32_length]; decide)]

theorem callee : CalleeOk (P := params) md Impl.Md5.PPC64LE.compress :=
  ⟨compress_verified.1, by decide +kernel⟩

namespace Update

theorem update_verified : Verified PPC64LE.target Impl.Md5.PPC64LE.Stream.update Proof.Md5.updatePPC64LE :=
  have h := MdStream.PPC64LE.Update.verified (name := "vg_md5_compress") dims callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (fun _ _ _ _ hp => MdStream.PPC64LE.Update.agree₀ hp) (by taint_decide))
    (by decide +kernel) (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.PPC64LE.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified PPC64LE.target Impl.Md5.PPC64LE.Stream.finalize Proof.Md5.finalizePPC64LE :=
  have h := MdStream.PPC64LE.Finalize.verifiedD (name := "vg_md5_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
      (fun _ _ _ _ hp => MdStream.PPC64LE.Finalize.agree₀D hp) (by taint_decide))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => by
      have := h Spec.Md5.H0 m hr trivial hc
      exact this.trans (List.take_of_length_le (Nat.le_of_eq (md.digest_length _))),
      fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.PPC64LE.Finalize.satD params 16

end Finalize

end VG.Proof.Md5.PPC64LE.Stream
