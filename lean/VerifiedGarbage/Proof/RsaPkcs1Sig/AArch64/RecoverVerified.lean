import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_pkcs1_recover` on AArch64: `Verified`

The shared contract (`Spec.RsaPkcs1Sig.recoverContract`, with the stack of
the frame and the callee, `stk`) from correctness (`code_ok`), constant time
(`code_ct`) and a state meeting the precondition (`sat`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk stackArgs_three)

theorem code_correct (c : PubChecked) (s : State)
    (h : (Spec.RsaPkcs1Sig.recoverContract abi (stk c.stack)).pre s) :
    ∃ t s', Exec isa (code c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.recoverContract abi (stk c.stack)).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c (preR_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, stackArgs_three,
    List.append_eq]
  exact hr

theorem code_constantTime (c : PubChecked) :
    ConstantTime isa (Spec.RsaPkcs1Sig.recoverContract abi (stk c.stack)).pre
      (Spec.RsaPkcs1Sig.recoverContract abi (stk c.stack)).pub (code c.name c.code) :=
  RelCT.constantTime ((code_ct c).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preR_of h₁, PubR.refl s₁⟩, preR_of h₂, pubR_of hp⟩) fun _ _ h => h)

/-- A state meeting the precondition: a 512-bit modulus, a one-byte `e`,
SHA-256, a one-byte signature, a working space of 1024 words, and the stack
pointer at `2^40`, far above them. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 32 | .x2 => 0x1000 | .x3 => 64 | .x4 => 0x2000 | .x5 => 1 | .x6 => 3
    | .x7 => 0x4000 | _ => 0
  sp := 0x10000000000
  mem a := if a = 0x10000000000 then 1 else if a = 0x1000000000A then 1
    else if a = 0x10000000011 then 4 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x10000000000, 24⟩]
  wr := [⟨0x5000, 32⟩, ⟨0x10000, 8192⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x10000 ∧ stackArg satState 2 = 1024 := by
  decide

theorem sat (K : Nat) (hK : K ≤ 2 ^ 20) : ∃ s, (Spec.RsaPkcs1Sig.recoverContract abi (stk K)).pre s := by
  refine ⟨satState, ?_⟩
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, stackArgs_three,
    List.append_eq]
  obtain ⟨a0, a1, a2⟩ := sat_args
  have hS : frameBytes + K - 1 + 1 = 2128 + K := by unfold frameBytes; omega
  have hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  have hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 (2128 + K)).toNat = 2 ^ 40 - (2128 + K) := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; omega
  have ha : stackArgAddr satState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, hS, ha]
  have kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (2128 + K), 2128 + K⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; omega)) (by dsimp only; rw [hkb]; omega)
      (by dsimp only; omega)
  refine ⟨by rw [hsp]; omega, by decide, by decide, by decide, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), kd _ _ (by decide),
    kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide),
    Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; omega))
      (by dsimp only; rw [hkb]; omega) (by dsimp only; rw [hsp]; omega),
    by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    ⟨.sha256, by decide, by decide⟩, by decide⟩

theorem code_verified (c : PubChecked) :
    Verified AArch64.target (code c.name c.code) (Spec.RsaPkcs1Sig.recoverContract abi (stk c.stack)) :=
  ⟨code_correct c, code_constantTime c, sat c.stack c.le⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
