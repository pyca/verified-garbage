import VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT
import VerifiedGarbage.Proof.MlKem1024.Arm.DecapsCT

/-!
# ML-KEM-1024 on 32-bit ARM: `vg_mlkem1024_keygen`, `Verified`

The key generation of `Proof/MlKem/Arm/KeyGenCT.lean` for `kl1024`: its precondition
from the contract's, and the contract's postcondition from what it shows.
-/

namespace VG.Proof.MlKem1024.Arm.KeyGen

open VG VG.Arm VG.Impl.MlKem.Arm VG.Impl.MlKem1024.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.Arm VG.Proof.MlKem1024.Arm
open VG.Proof.MlKem.Arm.Enc
open VG.Proof.MlKem.Arm.KeyGen hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Spec.MlKem1024.keyGenContract Arm.abi 8).pre s) : VG.Proof.MlKem.Arm.KeyGen.Pre kl1024 s := by
  sig_pre [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h0 : s.gpr .r0 = if okK kl1024 s₀ kl1024.k then 1 else 0)
    (hek : bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pEk s₀)) 1568 = VG.Proof.MlKem.Arm.KeyGen.EK kl1024 s₀)
    (hdk : bytesAt s.mem (State.addr (VG.Proof.MlKem.Arm.KeyGen.pDk s₀)) 3168 = VG.Proof.MlKem.Arm.KeyGen.DK kl1024 s₀) :
    (Spec.MlKem1024.keyGenContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  have e1 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r1)) 1568 = VG.Proof.MlKem.Arm.KeyGen.EK kl1024 s₀ := hek
  have e2 : bytesAt s.mem (BitVec.setWidth 64 (s₀.gpr .r2)) 3168 = VG.Proof.MlKem.Arm.KeyGen.DK kl1024 s₀ := hdk
  have eD : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0)) 32 = VG.Proof.MlKem.Arm.KeyGen.D s₀ := rfl
  have eZ : bytesAt s₀.mem (BitVec.setWidth 64 (s₀.gpr .r0) + 32) 32 = Z s₀ := rfl
  rw [e1, e2, eD, eZ]
  exact VG.Proof.MlKem.Arm.KeyGen.outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified Arm.target Impl.MlKem1024.Arm.keygen1024 (Spec.MlKem1024.keyGenContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h0, hek, hdk⟩ := VG.Proof.MlKem.Arm.KeyGen.correct (VG.Proof.MlKem1024.Arm.KeyGen.pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp⟩, VG.Proof.MlKem1024.Arm.KeyGen.post_of h0 hek hdk⟩
  · sig_pub [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    have hr : ρ₀ kl1024 s₁ = ρ₀ kl1024 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (VG.Proof.MlKem.Arm.KeyGen.all_ct ⟨VG.Proof.MlKem1024.Arm.KeyGen.pre_of h₁, VG.Proof.MlKem1024.Arm.KeyGen.pre_of h₂, hsp, h0, h1, h2, h3, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨VG.Proof.MlKem1024.Arm.KeyGen.satState, ?_⟩
    sig_sat_check [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem1024.Arm.KeyGen
