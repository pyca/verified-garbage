module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

def Ready (ps : List (Nat × Nat)) (L : Layout) (s : State) : Prop :=
  GoodV ps L s ∧ s.gpr .r8=off L.B (slot L.w aAcc+16) ∧ s.gpr .rbx=BitVec.ofNat 64 L.w

theorem pins_good : Pins GoodL [.rdi] := by
  rintro L s t ⟨mi,hs⟩ ⟨mj,ht⟩ r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r; exact hs.rdi.trans ht.rdi.symm

theorem pins_goodV (ps : List (Nat × Nat)) : Pins (GoodV ps) [.rdi] :=
  fun L s t hs ht => pins_good L s t hs.1 ht.1

theorem GoodV.of_outside {ps : List (Nat × Nat)} {L : Layout} {s t : State} (h : GoodV ps L s)
    (o : Outside L.B (slot L.w aAcc) (16*L.w+32) s.mem t.mem) (k : VG.Proof.MlKem.X86_64.Keep mmRegs s t) :
    GoodV ps L t := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega)⟩,
    hv.of_outside o (by unfold slot sFn hdrBytes; omega)⟩

/-- `GoodV` after code that changed the borrowed header words, then only the
accumulator. -/
theorem GoodV.of_bare {ps : List (Nat × Nat)} {L : Layout} {s t : State} (h : GoodV ps L s) {m : Mem}
    (o₁ : Outside L.B (8*sFn 12) 32 s.mem m) (o₂ : Outside L.B (slot L.w aAcc) (16*L.w+32) m t.mem)
    (k : VG.Proof.MlKem.X86_64.Keep mmRegs s t) : GoodV ps L t := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,
    (hg.hdr.of_outside_fn o₁ (by unfold sFn; omega)).of_outside o₂ (by unfold slot; omega)⟩,
    (hv.of_outside o₁ (Nat.le_refl _)).of_outside o₂ (by unfold slot sFn hdrBytes; omega)⟩

theorem setup_fw {ps : List (Nat × Nat)} {cb b : Nat} (pb : (cb, b) ∈ ps) (L : Layout) (s : State)
    (h : GoodV ps L s) : WP isa (.block (Adx.setup cb)) s (Ready ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (adxSetupV_ok hg.scr hg.rdi hg.hdr L.hZ (hv.at pb) (hv.lt pb)) fun _ ⟨_,_,p,w,m,k⟩ =>
    ⟨⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,m ▸ hv⟩,p,w⟩

theorem zero_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : Ready ps L s) :
    WP isa Adx.zeroWin8 s (GoodV ps L) := by
  obtain ⟨⟨⟨mi,hg⟩,hv⟩,p,w⟩ := h
  have pads := AdxHeader.pads_bound L.hZ
  have hw := L.hw
  refine WP.mono (zeroWin8_ok hg.scr p w L.hwN L.hn (by omega)
    (by unfold AdxHeader.highPad at pads; omega)) fun t ⟨_,o,k⟩ => ?_
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega)⟩,
    hv.of_outside o (by unfold slot sFn hdrBytes; omega)⟩

theorem save_fw {ps : List (Nat × Nat)} (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa AdxHeader.save s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  refine WP.mono (AdxHeader.save_ok hg.scr hg.rdi hg.hdr L.hZ) fun t ⟨_,_,f,k⟩ => ?_
  have o : Outside L.B (slot L.w aAcc) (16*L.w+32) s.mem t.mem := by
    intro x hx
    apply f x
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> unfold AdxHeader.highPad at * <;> omega
  exact ⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,hg.hdr.of_outside o (by unfold slot; omega)⟩,
    hv.of_outside o (by unfold slot sFn hdrBytes; omega)⟩

theorem raw_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup cb)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) h₂).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.rawProduct ca cb) (fun _ _ => True) := by
  unfold AdxTiledProduct.rawProduct
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_fw pb)) ?_
  refine RelCT.seq (two_piece [.r8,.rbx] ?_ (by taint_decide) zero_fw) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  have mapGood : ∀ L s, GoodV ps L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨⟨mi,hg⟩,_⟩; exact ⟨mi,hg,L.hZ⟩
  refine RelCT.seq (two_post (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.save_ct) save_fw) ?_
  exact RelCT.seq (rows_ct pa pb ha hb ha1 ha2 hb1 hb2 hR)
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.restore_ct)

theorem rawBare_ct {ps : List (Nat × Nat)} {ca cb a b : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup cb)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca cb)) h₂).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledProduct.rawProductBare ca cb) (fun _ _ => True) := by
  unfold AdxTiledProduct.rawProductBare
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_fw pb)) ?_
  refine RelCT.seq (two_piece [.r8,.rbx] ?_ (by taint_decide) zero_fw) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  have mapGood : ∀ L s, GoodV ps L s → GoodW ⟨L.B,L.Z,L.w⟩ s := by
    rintro L s ⟨⟨mi,hg⟩,_⟩; exact ⟨mi,hg,L.hZ⟩
  exact RelCT.seq (rows_ct pa pb ha hb ha1 ha2 hb1 hb2 hR)
    (two_map (fun L : Layout => (⟨L.B,L.Z,L.w⟩ : Ws)) mapGood AdxHeader.clear_ct)

end VG.Proof.Bignum.X86_64.AdxTiledProduct
