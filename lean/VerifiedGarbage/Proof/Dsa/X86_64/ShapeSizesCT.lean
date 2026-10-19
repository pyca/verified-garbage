module

public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
import VerifiedGarbage.Proof.Dsa.X86_64.WidthChoiceCT
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizes
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.WidthChoiceCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of both public width scans and size selection -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def ShapePStored (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ word s.mem p.base 176 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.pBytes).1 ∧
    word s.mem p.base Field.mask.offset = mask (decide (128 ≤ (VG.Proof.Dsa.significant p.pBytes).2.toNat))

def ShapeQScanned (p : ShapePublic) (s : State) : Prop :=
  ShapePStored p s ∧ s.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.qBytes).1 ∧
    s.gpr .r9 = (VG.Proof.Dsa.significant p.qBytes).2.zeroExtend 64

def ShapeQStored (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ word s.mem p.base 176 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.pBytes).1 ∧
    s.gpr .r8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.qBytes).1

theorem shapeP_ct : RelCT isa (Two (ShapeScanned ShapePublic.pBytes)) (.block shapeP) (Two ShapePStored) := by
  refine two_piece [.rdi] (pins_of (fun p _ => p.base) (by
    intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.rdi)) (by taint_decide) ?_
  intro p s ⟨h, h8, h9⟩
  exact WP.mono (shapeP_context h.scr h.rdi p.extentBound h8 h9) fun t ⟨hw, hm, hf, hk⟩ =>
    ⟨h.frame hf hk (by decide), hw, hm⟩

theorem shapeQScan_ct : RelCT isa (Two ShapePStored)
    (.seq (.block [.mov .rsi (.mem (Core.field .q)), .mov .rcx (.mem (Core.field .qLen))]) Checks.significant)
    (Two ShapeQScanned) := by
  refine two_post ((two_map (fun p : ShapePublic => p) (fun _ _ h => h.1)
    (shapeScan_ct .q .qLen ShapePublic.qPointer ShapePublic.qBytes
      (fun _ _ h => h.qPointer) (fun _ _ h => h.qLength) (fun _ _ h => h.qSource)
      ShapePublic.qPositive ShapePublic.qBound (by taint_decide))).mono
        (fun _ _ h => h) (fun _ _ _ => True.intro)) ?_
  intro p s ⟨h, hw, hm⟩
  exact WP.mono (scanField_ok h.scr h.rdi p.extentBound .q .qLen h.qPointer h.qLength h.qSource
    p.qPositive p.qBound) fun t ⟨h8, h9, he, hk⟩ =>
      ⟨⟨h.sameMem he hk (by decide), by rw [he]; exact hw, by rw [he]; exact hm⟩, h8, h9⟩

theorem shapeQ_ct : RelCT isa (Two ShapeQScanned) (.block shapeQ) (Two ShapeQStored) := by
  refine two_piece [.rdi] (pins_of (fun p _ => p.base) (by
    intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.1.rdi)) (by taint_decide) ?_
  intro p s ⟨⟨h, hw, hm⟩, h8, h9⟩
  exact WP.mono (shapeQ_context h.scr h.rdi p.extentBound h8 h9 hm)
    fun t ⟨_, _, hw', hf, hk⟩ => ⟨h.frame hf hk (by decide), hw'.trans hw, (hk.gpr (by decide)).trans h8⟩

theorem shapeWidth_ct : RelCT isa (Two ShapeQStored)
    (.seq (.block [.mov .rdx (.mem (hdr 22)), .alu .cmp .rdx (.imm 128)]) widthChoice)
    (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := fun p t => WidthChoicePre
    ((VG.Proof.Dsa.significant p.pBytes).1, (VG.Proof.Dsa.significant p.qBytes).1) t)
    [.rdi] (pins_of (fun p _ => p.base) (by
      intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.rdi))
    (by taint_decide) ?_) (two_map (fun p : ShapePublic =>
      ((VG.Proof.Dsa.significant p.pBytes).1, (VG.Proof.Dsa.significant p.qBytes).1))
      (fun _ _ h => h) widthChoice_ct)
  intro p s ⟨h, hw, h8⟩
  exact WP.mono (readWidth_ok h.scr h.rdi (Nat.le_trans (by decide) p.extentBound)
    (Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits _) p.pBound) hw)
    fun t ⟨hz, hd, _, hk⟩ => ⟨hd, (hk.gpr (by decide)).trans h8, hz⟩

theorem shapeSizes_ct : RelCT isa (Two ShapeContext) shapeSizes (fun _ _ => True) := by
  have h1 := shapeScan_ct .p .pLen ShapePublic.pPointer ShapePublic.pBytes
    (fun _ _ h => h.pPointer) (fun _ _ h => h.pLength) (fun _ _ h => h.pSource)
    ShapePublic.pPositive ShapePublic.pBound (by taint_decide)
  have h2 := fuseBlocks_ct (RelCT.seq shapeQ_ct shapeWidth_ct)
  have h3 := RelCT.seq shapeQScan_ct h2
  have h4 := fuseBlocks_ct (RelCT.seq shapeP_ct h3.assoc)
  exact (RelCT.seq h1 h4).assoc

end VG.Proof.Dsa.X86_64
