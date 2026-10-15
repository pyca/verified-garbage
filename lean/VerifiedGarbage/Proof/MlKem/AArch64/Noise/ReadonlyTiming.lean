module

public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
public import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem readonly_noise768_ct (kg : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.AgreeS ["VG_MLKEM_NTT16_ZETAS"] (Taint.ofRegs [.x28])) (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWith lay768 kg) := by
  cases kg <;>
    exact VG.Taint.constantTime (A:=taintS ["VG_MLKEM_NTT16_ZETAS"]) (Taint.ofRegs [.x28]) (fun _ _ _ _ h=>h) (by taint_decide)

theorem readonly_noise1024_ct (kg : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.AgreeS ["VG_MLKEM_NTT16_ZETAS"] (Taint.ofRegs [.x28]))
    (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWith Impl.MlKem1024.AArch64.lay1024 kg) := by
  cases kg <;>
    exact VG.Taint.constantTime (A:=taintS ["VG_MLKEM_NTT16_ZETAS"]) (Taint.ofRegs [.x28]) (fun _ _ _ _ h=>h) (by taint_decide)

/-- Only the rank and scratch extent enter the paired-noise instruction stream. -/
theorem readonly_noiseAll_congr {L M : KemLay} (hk : L.k=M.k) (hs : L.scl=M.scl) (kg : Bool) :
    Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWith L kg = Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWith M kg := by
  simp only [Impl.MlKem.AArch64.Noise.noiseAllWith,Impl.MlKem.AArch64.Noise.noisePairWith,
    Impl.MlKem.AArch64.Noise.noiseInit,Impl.MlKem.AArch64.Noise.noiseOutWith,
    Impl.MlKem.AArch64.Noise.noiseOff,KG.sOff,KG.SH,KEM.yOff,KEM.YH,hk,hs]

theorem readonly_noiseAll_ct {L : KemLay} (hL : (L.k=3 ∧ L.scl=32768) ∨ (L.k=4 ∧ L.scl=49152))
    (kg : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.AgreeS ["VG_MLKEM_NTT16_ZETAS"] (Taint.ofRegs [.x28])) (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWith L kg) := by
  rcases hL with ⟨hk,hs⟩ | ⟨hk,hs⟩
  · rw [readonly_noiseAll_congr (M:=lay768) hk hs]
    exact readonly_noise768_ct kg
  · rw [readonly_noiseAll_congr (M:=Impl.MlKem1024.AArch64.lay1024) hk hs]
    exact readonly_noise1024_ct kg

end VG.Proof.MlKem.AArch64.Noise
