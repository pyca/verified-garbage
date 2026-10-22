module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageCopy
public import VerifiedGarbage.Proof.MillerRabin.X86.OperandFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Round

/-! # Seed the public power table with Montgomery one and the witness -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem table_copies {σ s : State} {base : Addr} {bytes w : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes)
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.seq (VG.Impl.MillerRabin.X86.copy 11 9)
      (.seq (VG.Impl.MillerRabin.X86.copy 12 5) (VG.Impl.MillerRabin.X86.copy 6 5))) s fun t =>
      Stage base bytes w σ t ∧
      numAt t.mem base w 11 = numAt s.mem base w 9 ∧
      numAt t.mem base w 12 = numAt s.mem base w 5 ∧
      numAt t.mem base w 6 = numAt s.mem base w 5 ∧
      numAt t.mem base w 5 = numAt s.mem base w 5 := by
  refine WP.seq (WP.mono (h.copy hw hu hf (by decide) (by decide) (by decide)
    (.inr (.inr (.inr ⟨by decide, by decide⟩))) width) ?_)
  rintro s₁ ⟨v₁, h₁, f₁, _⟩
  have x₁ := array_frame_num h.context.ws.nowrap hf (show 5 < 28 by decide) (show 11 < 28 by decide)
    (by decide) f₁
  refine WP.seq (WP.mono (h₁.copy hw hu hf (by decide) (by decide) (by decide)
    (.inr (.inr (.inr ⟨by decide, by decide⟩))) width) ?_)
  rintro s₂ ⟨v₂, h₂, f₂, _⟩
  have x₂ := array_frame_num h₁.context.ws.nowrap hf (show 5 < 28 by decide) (show 12 < 28 by decide)
    (by decide) f₂
  have o₂ := array_frame_num h₁.context.ws.nowrap hf (show 11 < 28 by decide) (show 12 < 28 by decide)
    (by decide) f₂
  refine WP.mono (h₂.copy hw hu hf (by decide) (by decide) (by decide) (.inr (.inl rfl)) width) ?_
  rintro t ⟨v₃, ht, f₃, _⟩
  have x₃ := array_frame_num h₂.context.ws.nowrap hf (show 5 < 28 by decide) (show 6 < 28 by decide)
    (by decide) f₃
  have o₃ := array_frame_num h₂.context.ws.nowrap hf (show 11 < 28 by decide) (show 6 < 28 by decide)
    (by decide) f₃
  have t₃ := array_frame_num h₂.context.ws.nowrap hf (show 12 < 28 by decide) (show 6 < 28 by decide)
    (by decide) f₃
  exact ⟨ht, o₃.trans (o₂.trans v₁), t₃.trans (v₂.trans x₁),
    v₃.trans (x₂.trans x₁), x₃.trans (x₂.trans x₁)⟩

end VG.Proof.MillerRabin.X86
