module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
import VerifiedGarbage.Proof.TripleDes.AArch64.Link
import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Link
meta import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Triple DES-CBC decryption on AArch64 meets its contracts

`cbcDecryptChained_wp`: the modes' CBC decryption that updates the chaining
value (`Proof.Modes.AArch64.cbcDecryptChained_wp`) over Triple DES's core
for decryption (`dirCoreSpec`, calling the block function), with the
feedback modes' precondition (`fbPre`, as the IV is written too).
`cbcDecryptChained_verified`: it is correct and constant time, by the taint
analysis with public values in vector registers (`VectorTaint`) and the
block function's summary (`decSum`): the pointers, `n` and the stack
pointer are public, and so is everything the code computes from them; the
IV is secret. `cbcDecryptChained_framed` runs it with its working space on
the stack, zeroed on return: 1008 bytes, the 125 words of the scratch
buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- CBC decryption on AArch64 that updates the chaining value. -/
def cbcDecAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0))) (ivOf s)
        (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- The core's cipher is the contract's. -/
theorem invCipher_eq (k : Spec.TripleDes.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.TripleDes.invCipher k := rfl

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 125⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp (dirCoreSpec .decrypt) (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one] at hdata hiv
  rw [invCipher_eq] at hdata
  refine ⟨?_, ?_⟩
  · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
  · change _ = Spec.Cbc.next _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq]; exact hiv

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained (Proof.TripleDes.cbcDecChainedScratchContract AArch64.abi 125) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcDecryptChained_keeps_x30 (cbcDecryptChained_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun s₁ s₂ h₁ h₂ hp => ⟨fbTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
        simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [decSum])) (by
    sig_implies [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, cbcDecAArch64, fbPre, fbPub, AArch64.abi,
      AArch64.argRegs] [fbSat] using fbSat)

theorem cbcDecFrameSat_pre : ∃ s, (Spec.TripleDes.cbcDecryptChainedContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cbcDecryptChainedContract, Spec.TripleDes.cbcChainedSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cbcDecryptChained)
      (Spec.TripleDes.cbcDecryptChainedContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cbcDecryptChained_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-! ## Encryption -/

end VG.Proof.TripleDes.AArch64
