module

import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.Round
meta import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # Relational leakage proofs for the three Montgomery stages -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

/-- Metadata may contain a different secret inverse in each run. -/
def StageReady (base : BitVec 32) (size tmp a b mod acc n i ptr : Nat) (s : State) : Prop :=
  RoundCtx s base size tmp a b mod acc n ∧
  (∃ inv, RoundMeta s.mem base tmp a b mod acc n i inv) ∧
  s.gpr .r0 = base + BitVec.ofNat 32 ptr

theorem pair_posts {P Q : State → Prop} {code : Prog isa}
    (ct : RelCT isa (fun s t => P s ∧ P t) code (fun _ _ => True))
    (wp : ∀ s, P s → WP isa code s Q) :
    RelCT isa (fun s t => P s ∧ P t) code (fun s t => Q s ∧ Q t) :=
  (ct.wp (fun s t h => ⟨wp s h.1, wp t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem productStage_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n) :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i tmp s ∧
      StageReady base size tmp a b mod acc n i tmp t) productStage (fun _ _ => True) := by
  let P := StageReady base size tmp a b mod acc n i tmp
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block productArgs) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨cs, ⟨is, hs⟩, ps⟩ := h.1
    obtain ⟨ct, ⟨it, ht⟩, pt⟩ := h.2
    exact productArgs_ct (a := a + 4 * i) (by have := cs.tmpFits; omega)
      s t tr1 tr2 u v ⟨cs.workspace, ct.workspace, ps, pt, hs.aPtr, ht.aPtr⟩ e1 e2
  have wp (s : State) (h : P s) : WP isa (.block productArgs) s Q := by
    obtain ⟨ctx, ⟨inv, hdr⟩, ptr⟩ := h
    have fits := ctx.aFits
    exact WP.mono (productArgs_ok s ctx.workspace ctx.tmpFits (by omega)
      ptr hdr.aPtr hdr.count hdr.bPtr hdr.accPtr) (fun _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)
  unfold productStage
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨rowFull_ct s t tr1 tr2 u v trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩

end VG.Proof.Bignum.Arm
