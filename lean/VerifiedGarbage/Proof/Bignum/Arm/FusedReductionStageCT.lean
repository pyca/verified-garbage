module

public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.FusedReductionCT
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Cancellation writes the shifted result without leaking secret limbs. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem fusedReductionStage_relCT {base : BitVec 32} {size tmp a b mod acc n i : Nat} :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i (acc + 4 * n) s ∧
      StageReady base size tmp a b mod acc n i (acc + 4 * n) t) fusedReductionStage (fun s t => s.gpr .r0=t.gpr .r0) := by
  let P := StageReady base size tmp a b mod acc n i (acc + 4 * n)
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 mod ∧ s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block reductionArgs) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨cs, ⟨is, hs⟩, ps⟩ := h.1
    obtain ⟨ct, ⟨it, ht⟩, pt⟩ := h.2
    have layout := cs.layout
    have fits := cs.tmpFits
    apply reductionArgs_ct (base := base) (size := size) (top := acc + 4 * n) (acc := acc) (by omega) s t tr1 tr2 u v ?_ e1 e2
    refine ⟨cs.workspace, ct.workspace, ps, pt, ?_, ?_⟩
    · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega] using hs.accPtr
    · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega] using ht.accPtr
  have wp (s : State) (h : P s) : WP isa (.block reductionArgs) s Q := by
    obtain ⟨ctx, ⟨inv, hdr⟩, ptr⟩ := h
    have layout := ctx.layout
    have fits := ctx.tmpFits
    refine WP.mono (reductionArgs_ok s (acc := acc) (mod := mod) (n := n) inv ctx.workspace
      (by omega) (by omega) ptr ?_ ?_ ?_ ?_) (fun _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)
    · simpa only [show acc + 4 * n + 16 = tmp by omega] using hdr.count
    · simpa only [show acc + 4 * n + 24 = tmp + 8 by omega] using hdr.mPtr
    · simpa only [show acc + 4 * n + 28 = tmp + 12 by omega] using hdr.inverse
    · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega] using hdr.accPtr
  unfold fusedReductionStage
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact FusedReduction.code_relCT s t tr1 tr2 u v
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2


theorem fusedReductionStage_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i (acc + 4 * n) s ∧
      StageReady base size tmp a b mod acc n i (acc + 4 * n) t) fusedReductionStage (fun _ _ => True) :=
  fusedReductionStage_relCT.mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
