module

import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ProductArgs
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.ShiftArgs
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import Batteries.Logic
import VerifiedGarbage.Proof.Bignum.Arm.RowFullCT
import VerifiedGarbage.Proof.Bignum.Arm.ShiftCT
import VerifiedGarbage.Proof.Bignum.Arm.Shift
meta import VerifiedGarbage.Impl.Bignum.Arm.Round
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.ShiftStep
import VerifiedGarbage.Proof.Bignum.Arm.WideMath
import VerifiedGarbage.Proof.Bignum.Arm.WideValue
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.Arm.Target

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

theorem reductionStage_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i (acc + 4 * n) s ∧
      StageReady base size tmp a b mod acc n i (acc + 4 * n) t) reductionStage (fun _ _ => True) := by
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
  unfold reductionStage
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨rowFull_ct s t tr1 tr2 u v trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩


theorem quotientStage_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i (acc + 4 * n) s ∧
      StageReady base size tmp a b mod acc n i (acc + 4 * n) t) quotientStage (fun _ _ => True) := by
  let P := StageReady base size tmp a b mod acc n i (acc + 4 * n)
  let Q := fun s : State => ShiftCtx s base size acc (n + 1) ∧
    s.gpr .r0 = base + BitVec.ofNat 32 acc ∧ s.gpr .lr = BitVec.ofNat 32 (n + 1)
  let R := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * (n + 1))
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block shiftArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    simpa only [List.mem_singleton, forall_eq] using h.1.2.2.trans h.2.2.2.symm
  have wp (s : State) (h : P s) : WP isa (.block shiftArgs) s Q := by
    obtain ⟨ctx, ⟨inv, hdr⟩, ptr⟩ := h
    have layout := ctx.layout
    have fits := ctx.tmpFits
    refine WP.mono (shiftArgs_ok s (acc := acc) (n := n) ctx.workspace (by omega) ptr ?_ ?_) ?_
    · simpa only [show acc + 4 * n + 16 = tmp by omega] using hdr.count
    · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega] using hdr.accPtr
    · rintro t ⟨p0, count, _, keep⟩
      exact ⟨⟨ctx.workspace.nowrap, by omega, by rw [keep.wr]; exact ctx.workspace.writable⟩, p0, count⟩
  have shiftCT : RelCT isa (fun s t => Q s ∧ Q t) shift (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨shift_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have shiftWP (s : State) (h : Q s) : WP isa shift s R :=
    WP.mono (shift_ok s h.1 (by omega) h.2.1 h.2.2) (fun _ h => h.ptr)
  unfold quotientStage
  refine (pair_posts ct wp).seq ((pair_posts shiftCT shiftWP).seq ?_)
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  simpa only [List.mem_singleton, forall_eq] using h.1.trans h.2.symm

end VG.Proof.Bignum.Arm
