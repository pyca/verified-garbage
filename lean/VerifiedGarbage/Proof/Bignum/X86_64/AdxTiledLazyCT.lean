module
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxLazy8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxLazy8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The lazy final subtraction: constant time

`lazy8` addresses only from `w` and the bases of `T`, `m` and `o`, which
`lazyLoads` reads from the header; the mask, which is secret, only selects
data.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

/-- After `lazyLoads`: `w` and the bases of `T`, `o` and `m`. -/
def FL (o : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .r8 = off L.B (slot L.w aTmp) ∧
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w aN)

theorem pins_fl (o : Nat) : Pins (FL o) [.r12, .r8, .rbx, .r10] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

/-- `redcLazy`, for slots and layouts given by any public data `x`. -/
theorem redcLazy_ct {α : Type} {P : α → List (Nat × Nat)} {L : α → Layout} {O : α → Nat} {co : Nat}
    (po : ∀ x, (co, O x) ∈ P x) {h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.lazyLoads co)) h₃).isSome=true) :
    RelCT isa (Two fun x s => GoodV (P x) (L x) s) (AdxTiledProduct.redcLazy co) (fun _ _ => True) := by
  have pins : Pins (fun x s => GoodV (P x) (L x) s) [.rdi] := fun x => pins_goodV (P x) (L x)
  unfold AdxTiledProduct.redcLazy
  refine RelCT.seq redcV_ct' ?_
  refine RelCT.seq (two_piece (Ψ := fun x s => GoodV (P x) (L x) s ∧ s.gpr .r10=off (L x).B (slot (L x).w aN))
    [.rdi] pins (by taint_decide) ?_) ?_
  · rintro x s ⟨⟨mi,hg⟩,hv⟩
    have hZ := (L x).hZ
    have hsrc : readSrc s (.mem (hdr (sArr aN)))=some (off (L x).B (slot (L x).w aN)) := by
      rw [readSrc_word (d := 8*sArr aN) hg.scr (by simp only [State.ea,hdr,hg.rdi,hdrOff])
        (by have := hdr_lt_slot (L x).w 8 (show sArr aN<32 by decide); omega),hg.hdr.harr aN (by decide)]
    exact WP.mono (movMem_ok s (dst := .r10) hsrc) fun _ ⟨p,_,_,k⟩ =>
      ⟨⟨⟨mi,hg.scr.congr k.keep.2.2,(k.keep.gpr (by decide)).trans hg.rdi,k.2.1 ▸ hg.hdr⟩,k.2.1 ▸ hv⟩,p⟩
  unfold Adx.lazy8
  refine RelCT.seq (two_piece (Ψ := fun x => FL (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) [.rdi]
    (fun x s t hs ht => pins x s t hs.1 ht.1) hF ?_)
    (two_taint _ (fun x => pins_fl (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) (by taint_decide))
  rintro x s ⟨⟨⟨mi,hg⟩,hv⟩,p⟩
  exact WP.mono (lazyLoads_ok hg.scr hg.rdi hg.hdr (L x).hZ (hv.at (po x)) (hv.lt (po x)))
    fun _ ⟨p12,p8,pbx,_,k⟩ => ⟨p12,p8,pbx,(k.gpr (by decide)).trans p⟩

end VG.Proof.Bignum.X86_64.AdxTiledProduct
