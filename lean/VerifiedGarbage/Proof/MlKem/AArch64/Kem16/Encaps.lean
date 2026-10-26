module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encrypt
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Impl.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Bounds
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.TCB.Artifact

/-! # The 16-bit hashing encapsulation's postcondition

`DoneW` and `post_ofW`: what the noise, `u`, `v` and the epilogue leave, and
the encapsulation's postcondition from it (for `Kem16P/Encaps.lean`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Encaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem
variable {P : KemLay}

/-- `Done` with `Â` stored with 16 bits. -/
structure DoneW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = (gE P s₀).1
  ct : bytesAt s.mem (kA s₀ 3) P.ctLen = KPke.ct P.params (aMW true P (enL P) s₀ mB) (ekE P s₀) (mE s₀) (gE P s₀).2

theorem post_ofW {s₀ sB s' : State} {mA : Mem} (hB : BInvW true P (enL P) s₀ mA (rhoE P s₀) (P.k * P.k) sB)
    (hD : DoneW P s₀ sB.mem (sB.gpr .x24) s') : (encapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => encapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.ekLen)
    (bytesAt s₀.mem (s₀.gpr .x1) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x2) 32, bytesAt s'.mem (s₀.gpr .x3) P.ctLen)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 = (gE P s₀).1 := hD.key
  have ct : bytesAt s'.mem (s₀.gpr .x3) P.ctLen =
      KPke.ct P.params (aMW true P (enL P) s₀ sB.mem) (ekE P s₀) (mE s₀) (gE P s₀).2 := hD.ct
  rw [key, ct, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show encapsInternal P.params 280 (ekE P s₀) (mE s₀) = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩
      (a := aMW true P (enL P) s₀ sB.mem) fun i hi j hj => hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show encapsInternal P.params 280 (ekE P s₀) (mE s₀) = none
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj hn]
    rfl

end VG.Proof.MlKem.AArch64.Encaps
