module

public import VerifiedGarbage.Impl.MlKem1024.RISCV64.Top
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem.RISCV64.KeyGen

import VerifiedGarbage.Proof.MlKem.RISCV64.KeyGenCT
import VerifiedGarbage.Proof.MlKem1024.RISCV64.Calls
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM-1024 on RISC-V: `vg_mlkem1024_keygen`, `Verified`

The function of `Proof/MlKem/RISCV64/KeyGenCT.lean` for `kl1024`: its
precondition from the contract's, and the contract's postcondition from what it
shows.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.RISCV64.KeyGen

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64 VG.Impl.MlKem1024.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem VG.Proof.MlKem.RISCV64 VG.Proof.MlKem1024.RISCV64
open VG.Proof.MlKem.RISCV64.Enc
open VG.Proof.MlKem.RISCV64.KeyGen hiding pre_of post_of satState verified

theorem pre_of {s : State} (h : (Spec.MlKem1024.keyGenContract RISCV64.abi 1168).pre s) : Pre kl1024 s := by
  sig_pre [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩ := h
  exact ⟨kl1024_wf, kl1024_calls, al, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩

theorem post_of {s₀ s : State} (h3 : s.gpr .a0 = if okK kl1024 s₀ kl1024.k then 1 else 0)
    (hek : bytesAt s.mem (pEk s₀) 1568 = EK kl1024 s₀)
    (hdk : bytesAt s.mem (pDk s₀) 3168 = DK kl1024 s₀) :
    (Spec.MlKem1024.keyGenContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32 (if okK kl1024 s₀ kl1024.k then (1 : BitVec 64) else 0) =
      if okK kl1024 s₀ kl1024.k then 1 else 0 := by
    cases okK kl1024 s₀ kl1024.k <;> rfl
  rw [h3, hek, hdk, e]
  exact outcome kl1024_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1568⟩, ⟨0x3000, 3168⟩, ⟨0x10000, 49152⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem1024.RISCV64.keygen1024 (Spec.MlKem1024.keyGenContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hek hdk⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρ₀ kl1024 s₁ = ρ₀ kl1024 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem1024.keyGenContract, Spec.MlKem1024.keyGenSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem1024.RISCV64.KeyGen
