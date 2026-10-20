module

public import VerifiedGarbage.Proof.MdStream.AArch64.Update
meta import VerifiedGarbage.Proof.MdStream.AArch64.Update
public import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
meta import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
import VerifiedGarbage.Proof.MdStream.AArch64.Words
meta import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Out
meta import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Out
public import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
meta import VerifiedGarbage.Proof.Sha256.AArch64.Compress
public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import VerifiedGarbage.Proof.Sha256.AArch64.Contract
meta import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Proof.Sha256.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha256.AArch64.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming SHA-256 on AArch64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/AArch64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/AArch64/`) for SHA-256's instance (`Proof/Sha256/Md.lean`),
given what SHA-256's own pieces do: its length field and digest (`shape`), that
its compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64

abbrev params := Impl.Sha256.AArch64.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  lenKeepsV := by decide +kernel
  outKeepsV := by decide +kernel
  len _ hout := len64_ok (d := params.N + params.B - params.L) (be := true) (by decide) hout
  out _ hin hout hd := by
    refine (out256_ok hin hout).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sha256.AArch64.compress :=
  ⟨compress_verified.1, by lit_decide, by lit_decide⟩

namespace Update

theorem update_verified : Verified AArch64.target Impl.Sha256.AArch64.Stream.update Proof.Sha256.updateAArch64 :=
  have h := MdStream.AArch64.Update.verified (name := "vg_sha256_compress") dims callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun _ _ _ _ hp => MdStream.AArch64.Update.agree₀ hp) (by taint_decide))
    (instrs_keeps (by lit_decide)) (by lit_decide)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified AArch64.target Impl.Sha256.AArch64.Stream.finalize Proof.Sha256.finalizeAArch64 :=
  have h := MdStream.AArch64.Finalize.verified (name := "vg_sha256_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
      (fun _ _ _ _ hp => MdStream.AArch64.Finalize.agree₀ hp) (by taint_decide))
    (instrs_keeps (by lit_decide)) (by lit_decide)
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Finalize.sat params

theorem writeW_rev32 (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev32 w) = Proof.Sha256.Stream.writeBytes m a (Spec.Sha256.wordBytes w) :=
  writeW32 m a true w

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := setWidth32 v

theorem flat_length (H : Spec.Sha256.HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap Spec.Sha256.wordBytes).length = 4 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (Spec.Sha256.wordBytes w).length = 4 := fun w _ => rfl
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

end Finalize

end VG.Proof.Sha256.AArch64.Stream
