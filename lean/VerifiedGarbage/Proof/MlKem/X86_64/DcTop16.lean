module

public import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec
public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop

/-!
# ML-KEM on x86-64: the end of decapsulation's re-encryption, with 16-bit polynomials

The state after the re-encryption with 16-bit polynomials (`Enc16.lean`)
writes `c'` to `oCT16` (`EncO16`), the input of the choice of the key
(`EncO16.sel`), for `kemDecapsJ16_correct` (`DjFused16.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps16

open Decaps

/-- The end of the re-encryption. -/
abbrev EncO16 {K : Kem16} (W : Dc16Wf K) (σ s : State) : Prop :=
  Enc16.EOut16 K (dcX W.toDcWfB σ) (sc oCT16) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 s

theorem EncO16.sel {K : Kem16} {W : Dc16Wf K} {σ s : State} (h : EncO16 W σ s) : SelIn K.L oCT16 σ s :=
  ⟨h.out.1, h.out.2, h.r15, h.ct⟩

end Decaps16

end VG.Proof.MlKem.X86_64
