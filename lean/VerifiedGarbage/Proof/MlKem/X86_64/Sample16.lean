module
public import VerifiedGarbage.Impl.MlKem.X86_64.Sample
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.TCB.X86_64.Target

import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlKem.Bits

/-!
# ML-KEM on x86-64: `vg_mlkem16_sample_ntt`, verified

`vg_mlkem_sample_ntt`'s code with 16-bit stores (`sampleNTTW true`), whose
proofs are `vg_mlkem_sample_ntt`'s for either width (`sampleW_correct`,
`sampleW_ct`); `sampleKW true` implies the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sample16Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x3000, 2048⟩]

theorem sample16_verified :
    Verified X86_64.target Impl.MlKem.X86_64.sampleNTT16 (Proof.MlKem.sampleNTT16Contract X86_64.abi 16) :=
  Verified.of_correct (sampleW_correct true) (sampleW_ct true)
    { pre := by sig_implies_pre [Proof.MlKem.sampleNTT16Contract, Proof.MlKem.sampleNTT16Sig, sampleKW, cRegion, cw,
        X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlKem.sampleNTT16Contract, Proof.MlKem.sampleNTT16Sig, sampleKW, X86_64.abi, X86_64.argRegs]
        dsimp only [sampleKW] at h
        obtain ⟨hr, hp⟩ := h
        cases e : Spec.MlKem.sampleNTT Spec.MlKem.minIterations (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 34) with
        | none =>
          rw [e] at hr
          have h0 : BitVec.setWidth 32 (s'.gpr .rax) = 0 := hr
          exact ⟨fun h1 => absurd (h0.symm.trans h1) (by decide : (0 : BitVec 32) ≠ 1), .inr ⟨h0, e⟩⟩
        | some f =>
          rw [e] at hr
          have h1 : BitVec.setWidth 32 (s'.gpr .rax) = 1 := hr
          obtain ⟨hred, hf⟩ := hp f e
          exact ⟨fun _ => hred, .inl ⟨h1, Spec.MlKem.minIterations, by
            show Spec.MlKem.sampleNTT _ _ = _
            rw [e]; exact congrArg some hf.symm⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlKem.sampleNTT16Contract, Proof.MlKem.sampleNTT16Sig, sampleKW, X86_64.abi,
          X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx⟩ := h
        exact ⟨hdi, hsi, hdx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Proof.MlKem.sampleNTT16Contract, Proof.MlKem.sampleNTT16Sig, sampleKW, cRegion, cw,
        X86_64.abi, X86_64.argRegs] [sample16Sat] using sample16Sat }

end VG.Proof.MlKem.X86_64
