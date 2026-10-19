module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyEntryReady
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyBody

/-! # Saving caller registers leaves the precomputed public key unchanged -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

theorem FnInput.enteredCache {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : FnInput g bs s) : Precomputed g bs (entered s) ↔ Precomputed g bs s := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold verifyStack at this; omega
  have F := pushed_frame (rs := savedRegisters) (s := s) (by decide) low
  have saved : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
    rw [h.savedSp]
    exact h.context.valid.offsetAddr (by decide)
  unfold below at F
  rw [← pushed_esp] at F
  change Frame [⟨((pushed savedRegisters s).gpr .esp).setWidth 64, 16⟩] s.mem (entered s).mem at F
  rw [saved] at F
  have words : Spec.Rsa.wordsAt (entered s).mem (byteAddr (g.sources 4)) g.preLength =
      Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength :=
    VG.Proof.Rsa.wordsAt_frame F (by
      have fit := h.context.valid.sourceFits 4
      change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
      omega) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.context.valid.stackSources 4).sub_left h.context.valid.savedSub).symm)
  unfold Precomputed
  rw [words]

end VG.Proof.RsaPkcs1Sig.X86.Ver
