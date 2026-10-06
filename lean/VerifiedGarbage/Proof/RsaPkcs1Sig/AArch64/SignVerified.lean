import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_pkcs1_sign` on AArch64: `Verified`

The shared contract (`Spec.RsaPkcs1Sig.signContract`, with the stack of the
frame and the callee, `stk`) from correctness (`code_ok`), constant time
(`code_ct`) and a state meeting the precondition (`sat`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem sigOut_eq (s : State) :
    sigOut s = Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat) ((s.gpr .x6).setWidth 32).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) := by
  rw [signId_eq, bytesAt_length]
  rfl

theorem code_correct (c : PrivChecked) (s : State)
    (h : (Spec.RsaPkcs1Sig.signContract abi (stk c.stack)).pre s) :
    ∃ t s', Exec isa (code c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Sig.signContract abi (stk c.stack)).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c (preS_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq]
  rw [← sigOut_eq]
  exact hr

theorem code_constantTime (c : PrivChecked) :
    ConstantTime isa (Spec.RsaPkcs1Sig.signContract abi (stk c.stack)).pre
      (Spec.RsaPkcs1Sig.signContract abi (stk c.stack)).pub (code c.name c.code) :=
  RelCT.constantTime ((code_ct c).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preS_of h₁, PubS.refl s₁⟩, preS_of h₂, pubS_of hp⟩) fun _ _ h => h)

/-- A state meeting the precondition: a 512-bit modulus, one-byte `e`, hash
value and key parts, a working space of 1024 words, and the stack pointer at
`2^40`, far above them. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 64 | .x2 => 0x1000 | .x3 => 64 | .x4 => 0x2000 | .x5 => 1 | .x7 => 0x3000
    | _ => 0
  sp := 0x10000000000
  mem a := if a = 0x10000000000 then 1 else if a = 0x10000000009 then 0x60
    else if a = 0x10000000010 then 1 else if a = 0x10000000019 then 0x70
    else if a = 0x10000000020 then 1 else if a = 0x10000000029 then 0x80
    else if a = 0x10000000030 then 1 else if a = 0x10000000039 then 0x90
    else if a = 0x10000000040 then 1 else if a = 0x10000000049 then 0xA0
    else if a = 0x10000000050 then 1 else if a = 0x1000000005A then 1
    else if a = 0x10000000061 then 4 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x6000, 1⟩, ⟨0x7000, 1⟩, ⟨0x8000, 1⟩, ⟨0x9000, 1⟩,
    ⟨0xA000, 1⟩, ⟨0x10000000000, 104⟩]
  wr := [⟨0x5000, 64⟩, ⟨0x10000, 8192⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x6000 ∧ stackArg satState 2 = 1 ∧
    stackArg satState 3 = 0x7000 ∧ stackArg satState 4 = 1 ∧ stackArg satState 5 = 0x8000 ∧
    stackArg satState 6 = 1 ∧ stackArg satState 7 = 0x9000 ∧ stackArg satState 8 = 1 ∧
    stackArg satState 9 = 0xA000 ∧ stackArg satState 10 = 1 ∧ stackArg satState 11 = 0x10000 ∧
    stackArg satState 12 = 1024 := by
  decide

theorem sat (K : Nat) (hK : K ≤ 2 ^ 20) : ∃ s, (Spec.RsaPkcs1Sig.signContract abi (stk K)).pre s := by
  refine ⟨satState, ?_⟩
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := sat_args
  have hS : frameBytes + K - 1 + 1 = 1136 + K := by unfold frameBytes; omega
  have hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  have hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 (1136 + K)).toNat = 2 ^ 40 - (1136 + K) := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; omega
  have ha : stackArgAddr satState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hS, ha]
  have kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (1136 + K), 1136 + K⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; omega)) (by dsimp only; rw [hkb]; omega)
      (by dsimp only; omega)
  refine ⟨by rw [hsp]; omega, by decide, by decide, by decide, ?_⟩
  refine ⟨Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), ?_⟩
  refine ⟨Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), ?_⟩
  refine ⟨kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide),
    kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide), ?_⟩
  refine ⟨Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; omega))
      (by dsimp only; rw [hkb]; omega) (by dsimp only; rw [hsp]; omega), ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  exact ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem code_verified (c : PrivChecked) :
    Verified AArch64.target (code c.name c.code) (Spec.RsaPkcs1Sig.signContract abi (stk c.stack)) :=
  ⟨code_correct c, code_constantTime c, sat c.stack c.le⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
