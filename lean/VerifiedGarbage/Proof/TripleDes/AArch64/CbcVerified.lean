module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
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
value (`Proof.Modes.AArch64.cbcDecryptChained_wp`) over Triple DES's batched
core for decryption (`batchCoreSpec`, the bitsliced batch on 128 blocks),
with the batched modes' precondition (`batchPre`, as the IV is written too).
`vg_triple_des_cbc_decrypt_chained` runs it for eleven blocks or more
(`ShortCbc.lean`, which has its `Verified`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- CBC decryption on AArch64 that updates the chaining value. -/
def cbcDecAArch64 : Contract isa where
  pre := batchPre blkLen
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0))) (ivOf s)
        (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- The core's cipher is the contract's. -/
theorem invCipher_eq (k : Spec.TripleDes.Schedule) : (batchCoreSpec .decrypt).cipher k = Spec.TripleDes.invCipher k := rfl

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 140⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp (batchCoreSpec .decrypt) (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [batchCore_bw, Nat.mul_one] at hdata hiv
  rw [invCipher_eq] at hdata
  refine ⟨?_, ?_⟩
  · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
  · change _ = Spec.Cbc.next _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq]; exact hiv

theorem cbcDecFrameSat_pre : ∃ s, (Spec.TripleDes.cbcDecryptChainedContract AArch64.abi 1120).pre s := by
  implies_sat [Spec.TripleDes.cbcDecryptChainedContract, Spec.TripleDes.cbcChainedSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-! ## Encryption -/

end VG.Proof.TripleDes.AArch64
