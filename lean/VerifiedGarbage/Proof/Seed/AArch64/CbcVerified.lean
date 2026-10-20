module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
public import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Seed.AArch64.Link
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Seed.AArch64.Link
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SEED-CBC on AArch64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.AArch64.cbcEncryptChained_wp` and
`cbcDecryptChained_wp`) over SEED's core for each direction: decryption over
`dirCoreSpec .decrypt`, encryption over the feedback modes' core
(`fbCoreSpec`), with the IV's address in `x25`, which the core keeps in
`v31` (`keeps_x25`). `cbcEncryptChained_verified`,
`cbcDecryptChained_verified`: each is correct and constant time, by the
taint analysis with public values in vector registers (`VectorTaint`), as
for OFB and CFB (`fbPre`, `fbTaint_agree`): the pointers, `n` and the stack
pointer are public, and so is everything the code computes from them, which
it keeps in registers (the data's address and the blocks left in `v29` and
`v30` across the batch, which uses no vector instruction); the IV is
secret. `cbcEncryptChained_framed` and `cbcDecryptChained_framed` run them
with their working space on the stack, zeroed on return: 1456 bytes, the
182 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.Impl.Seed.AArch64

/-- CBC decryption on AArch64 that updates the chaining value. -/
def cbcDecAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.Seed.invCipher (Spec.Seed.scheduleAt s.mem (s.gpr .x0))) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on AArch64 that updates the chaining value. -/
def cbcEncAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

/-! ## Decryption -/

attribute [local irreducible] Spec.Seed.invCipher in
/-- The core's cipher is the contract's (stated once: unifying them unfolds the cipher's spec). -/
theorem decCipher_eq : (dirCoreSpec .decrypt).cipher = Spec.Seed.invCipher := rfl

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 182⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp (dirCoreSpec .decrypt) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Seed.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩) fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, show 8 * 2 = 16 from rfl] at hdata hiv
  rw [decCipher_eq] at hdata
  exact ⟨hdata, hiv⟩

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained (Proof.Seed.cbcDecChainedScratchContract AArch64.abi 182) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcDecryptChained_keeps_x30 (cbcDecryptChained_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig,
      Proof.Seed.cbcDecChainedPost, cbcDecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cbcDecFrameSat_pre : ∃ s, (Spec.Seed.cbcDecryptChainedContract AArch64.abi 1456).pre s := by
  implies_sat [Spec.Seed.cbcDecryptChainedContract, Spec.Seed.cbcChainedSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 cbcDecryptChained)
      (Spec.Seed.cbcDecryptChainedContract AArch64.abi 1456) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Seed.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1456) cbcDecryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Seed.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-! ## Encryption -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 182⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncryptChained_wp fbCoreSpec (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Seed.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩ keeps_x25)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [fbCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cbcEncryptChained_verified :
    Verified AArch64.target cbcEncryptChained (Proof.Seed.cbcEncChainedScratchContract AArch64.abi 182) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcEncryptChained_keeps_x30 (cbcEncryptChained_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig,
      Proof.Seed.cbcEncChainedPost, cbcEncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Seed.cbcEncryptChainedContract AArch64.abi 1456).pre s := by
  implies_sat [Spec.Seed.cbcEncryptChainedContract, Spec.Seed.cbcChainedSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x4 182 cbcEncryptChained)
      (Spec.Seed.cbcEncryptChainedContract AArch64.abi 1456) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Seed.cbcEncChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1456) cbcEncryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Seed.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Seed.AArch64
