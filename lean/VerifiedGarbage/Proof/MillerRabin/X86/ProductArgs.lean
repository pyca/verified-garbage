module

public import VerifiedGarbage.Proof.MillerRabin.X86.ArgumentState
public import VerifiedGarbage.Proof.MillerRabin.X86.Geometry
public import VerifiedGarbage.Proof.Bignum.X86.RtCall

/-! # The Montgomery adapter passes exactly the existing callable's arguments -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)
open VG.Proof.Bignum.X86.RtCall (callArg)

theorem productArgs_ok {f : State} {w o a b : Nat} {wsLen : BitVec 32}
    (hu : w ≤ 128)
    (width : readSrc f (.mem (sc 48)) = some (BitVec.ofNat 32 w))
    (length : readSrc f (.mem (sp (36 + savedLength))) = some wsLen)
    (widthApart : Region.Disjoint ⟨f.ea (sc 48), 4⟩ ⟨(f.gpr .esp).setWidth 64, 36⟩)
    (lengthApart : Region.Disjoint ⟨f.ea (sp (36 + savedLength)), 4⟩ ⟨(f.gpr .esp).setWidth 64, 36⟩)
    (low : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (fr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (productArgs o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        callArg (f.gpr .edi) wsLen w 256 56 (scratch w) (arrAt w o) (arrAt w a) (arrAt w b) i := by
  let values := callArg (f.gpr .edi) wsLen w 256 56 (scratch w) (arrAt w o) (arrAt w a) (arrAt w b)
  have I₀ := ArgumentState.initial f values
  simp only [productArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine I₀.store (by decide) low fr rfl fun s₁ I₁ => ?_
  refine wp_movS (I₁.read_source (by decide) length lengthApart) fun s₂ U₂ _ => ?_
  have I₂ := I₁.of_keeps (U₂.keeps.mono (by decide)) U₂.mem
  refine I₂.store (by decide) low fr U₂.gpr fun s₃ I₃ => ?_
  refine wp_movS (I₃.read_source (by decide) width widthApart) fun s₄ U₄ _ => ?_
  have I₄ := I₃.of_keeps (U₄.keeps.mono (by decide)) U₄.mem
  refine I₄.store (by decide) low fr U₄.gpr fun s₅ I₅ => ?_
  refine wp_movS rfl fun s₆ U₆ _ => ?_
  have I₆ := I₅.of_keeps (U₆.keeps.mono (by decide)) U₆.mem
  refine I₆.store (by decide) low fr U₆.gpr fun s₇ I₇ => ?_
  refine wp_movS rfl fun s₈ U₈ _ => ?_
  have I₈ := I₇.of_keeps (U₈.keeps.mono (by decide)) U₈.mem
  refine I₈.store (by decide) low fr U₈.gpr fun s₉ I₉ => ?_
  refine scratchOffset_ok (I₉.read_source (by decide) width widthApart) fun s₁₀ K₁₀ m₁₀ V₁₀ => ?_
  have I₁₀ := I₉.of_keeps (K₁₀.mono (by decide)) m₁₀
  refine I₁₀.store (by decide) low fr V₁₀ fun s₁₁ I₁₁ => ?_
  refine arrayOffset_ok (by decide) (I₁₁.read_source (by decide) width widthApart) hu fun s₁₂ K₁₂ m₁₂ V₁₂ _ => ?_
  have I₁₂ := I₁₁.of_keeps K₁₂ m₁₂
  refine I₁₂.store (by decide) low fr V₁₂ fun s₁₃ I₁₃ => ?_
  refine arrayOffset_ok (by decide) (I₁₃.read_source (by decide) width widthApart) hu fun s₁₄ K₁₄ m₁₄ V₁₄ _ => ?_
  have I₁₄ := I₁₃.of_keeps K₁₄ m₁₄
  refine I₁₄.store (by decide) low fr V₁₄ fun s₁₅ I₁₅ => ?_
  refine arrayOffset_ok (by decide) (I₁₅.read_source (by decide) width widthApart) hu fun s₁₆ K₁₆ m₁₆ V₁₆ _ => ?_
  have I₁₆ := I₁₅.of_keeps K₁₆ m₁₆
  refine I₁₆.store (by decide) low fr V₁₆ fun s₁₇ I₁₇ => WP.block_nil ⟨I₁₇.keeps, I₁₇.frame, I₁₇.words⟩

end VG.Proof.MillerRabin.X86
