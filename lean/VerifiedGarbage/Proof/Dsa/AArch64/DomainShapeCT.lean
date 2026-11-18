module

public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizes
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeTail
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizes
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.WidthChoice
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.WidthChoice
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeTail
meta import VerifiedGarbage.Proof.Dsa.AArch64.Masks
public import VerifiedGarbage.Proof.Dsa.AArch64.OddCheck
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.OddCheck
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Dsa.AArch64.ShapeTailCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.LastByteCT`, which only this module used -/

section

/-! # Timing of the final-byte reads in public domain checks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem lastByte_ct (fp fl : Field) (r : Reg) (pointer : ShapePublic → Addr) (bytes : ShapePublic → List Byte)
    (hptr : ∀ p s, ShapeContext p s → word s.mem p.base fp.offset = pointer p)
    (hlen : ∀ p s, ShapeContext p s → word s.mem p.base fl.offset = BitVec.ofNat 64 (bytes p).length)
    {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0])
      (.block [Core.field .x1 fp, Core.field .x9 fl]) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x1, .x9])
      (.block [.subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb r .x1 0]) h₂).isSome = true) :
    RelCT isa (Two ShapeContext) (.block [Core.field .x1 fp, Core.field .x9 fl,
      .subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb r .x1 0]) (fun _ _ => True) := by
  apply RelCT.block_append (M := isa) (l₁ := [Core.field .x1 fp, Core.field .x9 fl])
    (l₂ := [.subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb r .x1 0])
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .x1 = pointer p ∧
    s.gpr .x9 = BitVec.ofNat 64 (bytes p).length) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.x0)) ht₁ ?_) ?_
  · intro p s h
    brun [field_enc fp, field_enc fl, Core.field, h.x0, fieldAddress, hptr p s h, hlen p s h,
      h.scr.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 p.extentBound),
      h.scr.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 p.extentBound)]
  · exact two_taint [.x1, .x9] (pins_of (fun p r => if r = .x1 then pointer p else BitVec.ofNat 64 (bytes p).length) (by
      intro p s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) ht₂

theorem oddCheck_ct : RelCT isa (Two ShapeContext) (.block oddCheck) (fun _ _ => True) := by
  have hp := lastByte_ct .p .pLen .x3 ShapePublic.pPointer ShapePublic.pBytes
    (fun _ _ h => h.pPointer) (fun _ _ h => h.pLength) (by taint_decide) (by taint_decide)
  have hq := lastByte_ct .q .qLen .x2 ShapePublic.qPointer ShapePublic.qBytes
    (fun _ _ h => h.qPointer) (fun _ _ h => h.qLength) (by taint_decide) (by taint_decide)
  have hp' : RelCT isa (Two ShapeContext)
      (.block [Core.field .x1 .p, Core.field .x9 .pLen,
        .subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb .x3 .x1 0]) (Two ShapeContext) := by
    refine two_post hp ?_
    intro p s h
    have hi : p.pBytes.length - 1 < p.pBytes.length := by have := p.pPositive; omega_using [this]
    exact WP.mono (lastByte_ok h.scr h.x0 p.extentBound .p .pLen .x3 h.pPointer h.pLength
      p.pPositive p.pBound (h.pSource.rd _ hi) (h.pSource.val _ hi))
      fun t ⟨_, hm, hk⟩ => h.sameMem hm hk (by decide)
  have hq' : RelCT isa (Two ShapeContext)
      (.block [Core.field .x1 .q, Core.field .x9 .qLen,
        .subImm .x .x9 .x9 1, .add .x .x1 .x1 .x9, .ldrb .x2 .x1 0]) (Two BasePublic) := by
    refine two_post (Ψ := fun p s => BasePublic p.base s) hq ?_ |>.mono
      (fun _ _ h => h) (fun _ _ h => ?_)
    · intro p s h
      have hi : p.qBytes.length - 1 < p.qBytes.length := by have := p.qPositive; omega_using [this]
      exact WP.mono (lastByte_ok h.scr h.x0 p.extentBound .q .qLen .x2 h.qPointer h.qLength
        p.qPositive p.qBound (h.qSource.rd _ hi) (h.qSource.val _ hi))
        fun t ⟨_, _, hk⟩ => (hk.gpr .x0 (by decide)).trans h.x0
    · obtain ⟨p, h1, h2⟩ := h
      exact ⟨p.base, h1, h2⟩
  unfold oddCheck
  rw [List.append_assoc, List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq hp' ?_
  apply RelCT.block_append
  exact RelCT.seq hq' (two_taint [.x0] pins_base (by taint_decide))

end VG.Proof.Dsa.AArch64

end

end

/-! # Timing of the oddness and digest-prefix selection tail -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ShapeTailPre (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ ∃ sizes valid : Bool,
    s.gpr .x3 = mask sizes ∧ word s.mem p.base Field.mask.offset = mask valid

def ShapeMasked (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ ∃ valid : Bool, word s.mem p.base Field.mask.offset = mask valid

theorem shapeAccumulate_ct : RelCT isa (Two ShapeTailPre) (.block Checks.accumulate) (Two ShapeMasked) := by
  refine two_piece [.x0] (pins_of (fun p _ => p.base) (by
    intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.x0)) (by taint_decide) ?_
  intro p s ⟨h, sizes, valid, ha, hm⟩
  exact WP.mono (accumulate_ok h.scr h.x0 p.extentBound ha hm) fun t ⟨hm', hf, hk⟩ =>
    ⟨h.frame (shape_outside hf (Or.inr (Or.inr rfl))) hk (by decide), sizes && valid, hm'⟩

theorem shapeOdd_ct : RelCT isa (Two ShapeMasked) (.block oddCheck)
    (Two (fun (p : ShapePublic) s => BasePublic p.base s)) := by
  refine two_post (two_map (fun p => p) (fun _ _ h => h.1) oddCheck_ct) ?_
  intro p s ⟨h, valid, hm⟩
  have hp : p.pBytes.length - 1 < p.pBytes.length := by have := p.pPositive; omega_using [this]
  have hq : p.qBytes.length - 1 < p.qBytes.length := by have := p.qPositive; omega_using [this]
  exact WP.mono (oddCheck_ok h.scr h.x0 p.extentBound h.pPointer h.qPointer h.pLength h.qLength
    p.pPositive p.pBound p.qPositive p.qBound (h.pSource.rd _ hp) (h.qSource.rd _ hq)
    (h.pSource.val _ hp) (h.qSource.val _ hq) hm)
    fun t ⟨_, _, hk⟩ => (hk.gpr .x0 (by decide)).trans h.x0

theorem shapeTail_ct : RelCT isa (Two ShapeTailPre) (.block shapeTail) (fun _ _ => True) := by
  unfold shapeTail
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq shapeAccumulate_ct ?_
  apply RelCT.block_append
  refine RelCT.seq shapeOdd_ct ?_
  exact two_map ShapePublic.base (fun _ _ h => h) (two_taint [.x0] pins_base (by taint_decide))

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ShapeSizesCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.WidthChoiceCT`, which only this module used -/

section

/-! # Constant time of the supported public-width switch -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def WidthChoicePre (p : Nat × Nat) (s : State) : Prop :=
  s.gpr .x2 = BitVec.ofNat 64 p.1 ∧ s.gpr .x8 = BitVec.ofNat 64 p.2 ∧
    (s.gpr .x6 == (0#64)) = decide (p.1 = 128)

theorem widthChoice_ct : RelCT isa (Two WidthChoicePre) widthChoice (fun _ _ => True) := by
  unfold widthChoice
  refine two_ite (fun p s t hs ht => by change some (s.gpr .x6 == (0#64)) = some (t.gpr .x6 == (0#64)); rw [hs.2.2, ht.2.2]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_taint [.x2] (pins_of (fun p _ => BitVec.ofNat 64 p.1) (by
      intro p s h r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact h.1.1)) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of both public width scans and size selection -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ShapePStored (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ word s.mem p.base 176 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.pBytes).1 ∧
    word s.mem p.base Field.mask.offset = mask (decide (128 ≤ (VG.Proof.Dsa.significant p.pBytes).2.toNat))

def ShapeQScanned (p : ShapePublic) (s : State) : Prop :=
  ShapePStored p s ∧ s.gpr .x8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.qBytes).1 ∧
    s.gpr .x10 = (VG.Proof.Dsa.significant p.qBytes).2.zeroExtend 64

def ShapeQStored (p : ShapePublic) (s : State) : Prop :=
  ShapeContext p s ∧ word s.mem p.base 176 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.pBytes).1 ∧
    s.gpr .x8 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p.qBytes).1

theorem shapeP_ct : RelCT isa (Two (ShapeScanned ShapePublic.pBytes)) (.block shapeP) (Two ShapePStored) := by
  refine two_piece [.x0] (pins_of (fun p _ => p.base) (by
    intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.x0)) (by taint_decide) ?_
  intro p s ⟨h, h8, h9⟩
  exact WP.mono (shapeP_context h.scr h.x0 p.extentBound h8 h9) fun t ⟨hw, hm, hf, hk⟩ =>
    ⟨h.frame hf hk (by decide), hw, hm⟩

theorem shapeQScan_ct : RelCT isa (Two ShapePStored)
    (.seq (.block [Core.field .x1 .q, Core.field .x9 .qLen]) Checks.significant)
    (Two ShapeQScanned) := by
  refine two_post ((two_map (fun p : ShapePublic => p) (fun _ _ h => h.1)
    (shapeScan_ct .q .qLen ShapePublic.qPointer ShapePublic.qBytes
      (fun _ _ h => h.qPointer) (fun _ _ h => h.qLength) (fun _ _ h => h.qSource)
      ShapePublic.qPositive ShapePublic.qBound (by taint_decide))).mono
        (fun _ _ h => h) (fun _ _ _ => True.intro)) ?_
  intro p s ⟨h, hw, hm⟩
  exact WP.mono (scanField_ok h.scr h.x0 p.extentBound .q .qLen h.qPointer h.qLength h.qSource
    p.qPositive p.qBound) fun t ⟨h8, h9, he, hk⟩ =>
      ⟨⟨h.sameMem he hk (by decide), by rw [he]; exact hw, by rw [he]; exact hm⟩, h8, h9⟩

theorem shapeQ_ct : RelCT isa (Two ShapeQScanned) (.block shapeQ) (Two ShapeQStored) := by
  refine two_piece [.x0] (pins_of (fun p _ => p.base) (by
    intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.1.x0)) (by taint_decide) ?_
  intro p s ⟨⟨h, hw, hm⟩, h8, h9⟩
  exact WP.mono (shapeQ_context h.scr h.x0 p.extentBound h8 h9 hm)
    fun t ⟨_, _, hw', hf, hk⟩ => ⟨h.frame hf hk (by decide), hw'.trans hw, (hk.gpr .x8 (by decide)).trans h8⟩

theorem shapeWidth_ct : RelCT isa (Two ShapeQStored)
    (.seq (.block [ldh .x2 22, .subImm .x .x6 .x2 128]) widthChoice)
    (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := fun p t => WidthChoicePre
    ((VG.Proof.Dsa.significant p.pBytes).1, (VG.Proof.Dsa.significant p.qBytes).1) t)
    [.x0] (pins_of (fun p _ => p.base) (by
      intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.1.x0))
    (by taint_decide) ?_) (two_map (fun p : ShapePublic =>
      ((VG.Proof.Dsa.significant p.pBytes).1, (VG.Proof.Dsa.significant p.qBytes).1))
      (fun _ _ h => h) widthChoice_ct)
  intro p s ⟨h, hw, h8⟩
  exact WP.mono (readWidth_ok h.scr h.x0 (Nat.le_trans (by decide) p.extentBound)
    (Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits _) p.pBound) hw)
    fun t ⟨hz, hd, _, hk⟩ => ⟨hd, (hk.gpr .x8 (by decide)).trans h8, hz⟩

theorem shapeSizes_ct : RelCT isa (Two ShapeContext) shapeSizes (fun _ _ => True) := by
  have h1 := shapeScan_ct .p .pLen ShapePublic.pPointer ShapePublic.pBytes
    (fun _ _ h => h.pPointer) (fun _ _ h => h.pLength) (fun _ _ h => h.pSource)
    ShapePublic.pPositive ShapePublic.pBound (by taint_decide)
  have h2 := fuseBlocks_ct (RelCT.seq shapeQ_ct shapeWidth_ct)
  have h3 := RelCT.seq shapeQScan_ct h2
  have h4 := fuseBlocks_ct (RelCT.seq shapeP_ct h3.assoc)
  exact (RelCT.seq h1 h4).assoc

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of the entire public DSA domain-shape check -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem domainShape_split {s t : State} {trace : List Leak}
    (h : Exec isa Checks.domainShape s trace t) :
    Exec isa (.seq shapeSizes (.block shapeTail)) s trace t := by
  exact h

theorem domainShape_ct : RelCT isa (Two ShapeContext) Checks.domainShape (fun _ _ => True) := by
  have hs : RelCT isa (Two ShapeContext) shapeSizes (Two ShapeTailPre) := by
    refine two_post shapeSizes_ct ?_
    intro p s h
    exact WP.mono (shapeSizes_ok h.scr h.x0 p.extentBound h.pPointer h.qPointer h.pLength h.qLength
      h.pSource h.qSource p.pPositive p.pBound p.qPositive p.qBound)
      fun t ⟨ha, hm, _, hf, hk⟩ => ⟨h.frame hf hk (by decide), _, _, ha, hm⟩
  have ht := RelCT.seq hs shapeTail_ct
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact ht _ _ _ _ _ _ hp (domainShape_split e₁) (domainShape_split e₂)

end VG.Proof.Dsa.AArch64
