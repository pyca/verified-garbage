module

import VerifiedGarbage.Proof.Dsa.X86_64.LastByteCT
public import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.LastByteCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Timing of the oddness and digest-prefix selection tail -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ShapeTailPre (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ ∃ sizes valid : Bool,
    s.gpr .rax = mask sizes ∧ word s.mem p.base Field.mask.offset = mask valid

def ShapeMasked (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ ∃ valid : Bool, word s.mem p.base Field.mask.offset = mask valid

theorem shapeAccumulate_ct : RelCT isa (Two ShapeTailPre) (.block Checks.accumulate) (Two ShapeMasked) := by
  refine two_piece [.rdi] (pins_of (fun p _ => p.base) (by
    intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.rdi)) (by taint_decide) ?_
  intro p s ⟨h, sizes, valid, ha, hm⟩
  exact WP.mono (accumulate_ok h.scr h.rdi p.extentBound ha hm) fun t ⟨hm', hf, hk⟩ =>
    ⟨h.frame (shape_outside hf (Or.inr (Or.inr rfl))) hk (by decide), sizes && valid, hm'⟩

theorem shapeOdd_ct : RelCT isa (Two ShapeMasked) (.block oddCheck)
    (Two (fun (p : ShapePublic) s => BasePublic p.base s)) := by
  refine two_post (two_map (fun p => p) (fun _ _ h => h.1) oddCheck_ct) ?_
  intro p s ⟨h, valid, hm⟩
  have hp : p.pBytes.length - 1 < p.pBytes.length := by have := p.pPositive; omega
  have hq : p.qBytes.length - 1 < p.qBytes.length := by have := p.qPositive; omega
  exact WP.mono (oddCheck_ok h.scr h.rdi p.extentBound h.pPointer h.qPointer h.pLength h.qLength
    p.pPositive p.pBound p.qPositive p.qBound (h.pSource.rd _ hp) (h.qSource.rd _ hq)
    (h.pSource.val _ hp) (h.qSource.val _ hq) hm)
    fun t ⟨_, _, hk⟩ => (hk.gpr (by decide)).trans h.rdi

theorem shapeTail_ct : RelCT isa (Two ShapeTailPre) (.block shapeTail) (fun _ _ => True) := by
  unfold shapeTail
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq shapeAccumulate_ct ?_
  apply RelCT.block_append
  refine RelCT.seq shapeOdd_ct ?_
  exact two_map ShapePublic.base (fun _ _ h => h) (two_taint [.rdi] pins_base (by taint_decide))

end VG.Proof.Dsa.X86_64
