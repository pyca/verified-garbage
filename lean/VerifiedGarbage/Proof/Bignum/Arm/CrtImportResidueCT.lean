module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtQSourceCT
public import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Copying the q residue has a trace independent of both secret residues -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_importResidue_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32}
    (sep : Region.Disjoint ⟨State.addr (crtQ g.base g.words), 8 * workspaceWords g.words⟩
      ⟨State.addr child, 8 * workspaceWords g.words⟩) :
    RelCT isa (fun s t => CrtSelected g bs1 child s ∧ CrtSelected g bs2 child t ∧ s.sp = t.sp)
      (.seq (.block CrtFn.qSource) (transferArray 1 6)) (fun _ _ => True) := by
  have source : RelCT isa (fun s t => CrtSelected g bs1 child s ∧ CrtSelected g bs2 child t ∧ s.sp = t.sp)
      (.block CrtFn.qSource) (fun _ _ => True) :=
    crt_qSource_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs child s) :
      WP isa (.block CrtFn.qSource) s
        (TransferArrayInput child (crtQ g.base g.words) (workspaceWords g.words) (workspaceWords g.words) g.words) := by
    refine WP.mono (crt_qSource_ok s h.1) ?_
    rintro t ⟨ptr, mem, rest⟩
    have sharedT := h.1.of_mem mem rest
    exact ⟨h.2.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.2.ptr), sharedT.buffers.context.q, sharedT.q, ptr, sep⟩
  exact crt_seq_ct source (fun s h => wp s h) (fun s h => wp s h)
    (transferArray_ct (by decide : 1 < 8) (by decide : 6 < 8))

end VG.Proof.Bignum.Arm
