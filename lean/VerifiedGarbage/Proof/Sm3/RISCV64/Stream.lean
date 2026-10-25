module

public import VerifiedGarbage.Proof.MdStream.RISCV64.Update
public meta import VerifiedGarbage.Proof.MdStream.RISCV64.Update
public import VerifiedGarbage.Proof.MdStream.RISCV64.Finalize
public meta import VerifiedGarbage.Proof.MdStream.RISCV64.Finalize
public import VerifiedGarbage.Proof.MdStream.RISCV64.Init
public meta import VerifiedGarbage.Proof.MdStream.RISCV64.Init
public import VerifiedGarbage.Proof.Sm3.Md
public meta import VerifiedGarbage.Proof.Sm3.Md
public import VerifiedGarbage.Proof.Sm3.RISCV64.Compress
public meta import VerifiedGarbage.Proof.Sm3.RISCV64.Compress
public import VerifiedGarbage.Impl.Sm3.RISCV64.Stream
public meta import VerifiedGarbage.Impl.Sm3.RISCV64.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.MdStream.RISCV64.Words
meta import VerifiedGarbage.Proof.MdStream.RISCV64.Words
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sm3.Stream
meta import VerifiedGarbage.Proof.Sm3.Stream
import all Init.Data.Nat.Bitwise.Basic

/-!
# Streaming SM3 on RISC-V

`init` stores the initial hash value (`Proof/MdStream/RISCV64/Init.lean`), and
`update` and `finalize` are the generic streaming code
(`Impl/MdStream/RISCV64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/RISCV64/`) for SM3's instance (`Proof/Sm3/Md.lean`), given
what SM3's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis accepts its code.
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64.Stream

open VG VG.RISCV64 VG.Proof.MdStream VG.Proof.MdStream.RISCV64
open VG.Impl.Sm3.RISCV64.Stream (params)

theorem callee : CalleeOk md Impl.Sm3.RISCV64.compress := ⟨compress_verified.1, by decide +kernel⟩

/-! ## The length field and the digest -/

theorem shape : ShapeD (P := params) md 32 where
  le := by decide
  len s hout := lenBE_ok (by decide) s hout
  out s hin hout hd := by
    refine (outBE_ok (n := 8) (by decide) s hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq, List.take_of_length_le (by rw [flat_length])]

/-! ## The functions -/

theorem init_verified : Verified RISCV64.target Impl.Sm3.RISCV64.Stream.init Proof.Sm3.initRISCV64 :=
  have h := MdStream.RISCV64.init_verified (n := 96) Spec.Sm3.iv.toList (by decide) (by decide)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0]) (fun _ _ _ _ h => initAgree h)
      (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun s _ _ h => by
      refine (repr_iff (m := [])).mpr (md.repr_nil (stateAt_eq fun k hk => ?_))
      rw [h k (by simpa using hk), getElem!_pos _ k (by simpa using hk), Vector.getElem_toList],
    fun _ _ _ _ h => h, h.2.2⟩

theorem update_verified : Verified RISCV64.target Impl.Sm3.RISCV64.Stream.update Proof.Sm3.updateRISCV64 :=
  have h := MdStream.RISCV64.Update.verified (P := params) (name := "vg_sm3_compress") (by decide) callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => MdStream.RISCV64.Update.agree₀ hp) (by taint_decide))
    ⟨MdStream.RISCV64.Update.sat 32, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.finalize Proof.Sm3.finalizeRISCV64 :=
  have h := MdStream.RISCV64.Finalize.verifiedD (P := params) (name := "vg_sm3_compress") (by decide) shape callee
    (keepsN_all _ (by decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
      (fun _ _ _ _ hp => MdStream.RISCV64.Finalize.agree₀ hp) (by taint_decide))
    ⟨MdStream.RISCV64.Finalize.sat 32 32, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => by
      have := h Spec.Sm3.iv m hr trivial hc
      exact this.trans (List.take_of_length_le (Nat.le_of_eq (md.digest_length _))),
      fun _ _ _ _ h => h, h.2.2⟩

end VG.Proof.Sm3.RISCV64.Stream
