module
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encrypt
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutTables
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.DecapsStart
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Bounds
public import VerifiedGarbage.Proof.MlKem.AArch64.KemB
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Target

/-! # The 16-bit decapsulation's postcondition and `J(z ‖ c)`

`DoneW` and `post_ofW`: what the re-encryption, the comparison and the
selection leave, and the decapsulation's postcondition from it; `tailJ_ok`:
`J(z ‖ c)` from the third state to `JB` (`Kem16.tailJ`), for
`Kem16P/Decaps.lean`. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
variable {prf : Nat→Nat→Prog isa}

/-- `cpr` with `Â` stored with 16 bits. -/
abbrev cprW (P : KemLay) (s₀ : State) (mB : Mem) : List Byte :=
  KPke.ct P.params (aMW true P (deL P) s₀ mB) (KPke.dkEk P.params (dkD P s₀)) (mD P s₀) (gD P s₀).2

/-- `Done` with `Â` stored with 16 bits. -/
structure DoneW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = if cD P s₀ = cprW P s₀ mB then (gD P s₀).1 else jD P s₀

theorem post_ofW {s₀ sB s' : State} {mA : Mem} (hB : BInvW true P (deL P) s₀ mA (rhoD P s₀) (P.k * P.k) sB)
    (hD : DoneW P s₀ sB.mem (sB.gpr .x24) s') : (decapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => decapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.dkLen)
    (bytesAt s₀.mem (s₀.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s₀.gpr .x2) 32)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 =
      if cD P s₀ = cprW P s₀ sB.mem then (gD P s₀).1 else jD P s₀ := hD.key
  rw [key, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩
      (a := aMW true P (deL P) s₀ sB.mem) fun i hi j hj => by rw [KPke.ekRho_dkEk]; exact hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = none
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj (by rw [KPke.ekRho_dkEk]; exact hn)]
    rfl

/-- `BInvW` carried over writes apart from `ρ` and `Â`, from the memory written. -/
theorem binv_move {w16 : Bool} {L : Layout} {s₀ s t : State} {mA : Mem} {ρ : List Byte} {n : Nat}
    (h : BInvW w16 P L s₀ mA ρ n s) (hk : KB P L s₀ t) (h24 : t.gpr .x24 = s.gpr .x24) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hρ : ∀ r ∈ rs, (R (kA s₀) L.sc SB 32).Disjoint r)
    (hA : ∀ e < n, ∀ r ∈ rs, (polyRegion (aP L s₀ e)).Disjoint r) : BInvW w16 P L s₀ t.mem ρ n t := by
  refine ⟨hk, Frame.refl _ _, ?_, by rw [h24]; exact h.acc, fun e he => reducedW_frame hf (hA e he) (h.red e he),
    fun e he => ?_⟩
  · rw [bytesAt_frame hf hρ (by decide)]; exact h.rho
  · rw [polyAtW_frame hf (hA e he)]; exact h.res e he

/-- `J(z ‖ c)`, the first 32 bytes of the third state, to `JB` (`Kem16.tailJ`). -/
theorem tailJ_ok {s₀ sB : State} (hp : Pre P (deL P) s₀) {ρ : List Byte} {n : Nat} (hn : n ≤ P.k * P.k)
    (hB : BInvW true P (deL P) s₀ sB.mem ρ n sB)
    (hst : Spec.Sha3.stateAt sB.mem (kA s₀ (deL P).sc) =
      Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 0x1f) (Hybrid.jE P s₀))) :
    WP isa (.block Impl.MlKem.AArch64.Kem16.tailJ) sB fun t =>
      BInvW true P (deL P) s₀ t.mem ρ n t ∧ t.gpr .x24 = sB.gpr .x24 ∧
      bytesAt t.mem (sA (deL P) s₀ JB) 32 = jD P s₀ ∧
      (∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ JB ∨ JB + 32 ≤ o) →
        bytesAt t.mem (sA (deL P) s₀ o) l = bytesAt sB.mem (sA (deL P) s₀ o) l) ∧
      Frame [R (kA s₀) (deL P).sc JB 32] sB.mem t.mem := by
  have hw := hp.wf
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 3) (D := kA s₀ 3) (so := KEM.ST) (dO := JB)
    (by decide) (by decide) (by decide) (by decide) (sdisj hp (by lom) (by lom) (by lom))
    hB.kb.x28 hB.kb.x28 (cov_sr hp hB.kb (by lom)) (cov_s hp hB.kb (by lom))) fun t ⟨k, f, b⟩ => ?_
  have kb := hB.kb.frame k f (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  have far : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ JB ∨ JB + 32 ≤ o) →
      bytesAt t.mem (sA (deL P) s₀ o) l = bytesAt sB.mem (sA (deL P) s₀ o) l := fun hf h => by
    refine bytesAt_frame f (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]; exact sdisj hp hf (by lom) h
  refine ⟨binv_move hB kb (k.get .x24) f (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact sdisj hp (by lom) (by lom) (by lom))
    (fun e he r hr => by
      rw [List.mem_singleton.mp hr]
      exact sdisj hp (o₁ := AH + 1024 * e) (l₁ := 1024) (by lom) (by lom) (.inr (by lom))),
    k.get .x24, ?_, far, f⟩
  rw [show sA (deL P) s₀ JB = kA s₀ 3 + BitVec.ofNat 64 JB from rfl, b,
    show KEM.ST = 0 from rfl, ptr_zero]
  show _ = J (Hybrid.jE P s₀)
  rw [J_eq, Hybrid.bytesAt_squeeze]
  show Spec.Sha3.squeezeFrom 136 (Spec.Sha3.stateAt sB.mem (kA s₀ (deL P).sc)) 0 32 = _
  rw [hst]; rfl

end VG.Proof.MlKem.AArch64.Decaps
