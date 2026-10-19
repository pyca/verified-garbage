module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.TripleDes.AArch64.Link
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Link
import VerifiedGarbage.Impl.Aes.AArch64.Alloc
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Loop
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.TripleDes.AArch64.Initial
import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundFunction
import VerifiedGarbage.Proof.TripleDes.AArch64.Store
import VerifiedGarbage.Proof.TripleDes.AArch64.Tail
import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.AArch64.Word
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.Words
meta import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.AArch64.Cfb8
meta import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Loop
meta import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Copy
meta import VerifiedGarbage.Proof.Modes.AArch64.Counter
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Unchain
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.CbcNext
meta import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
meta import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
meta import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
meta import VerifiedGarbage.Proof.Rc2.Select
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Box
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Initial
meta import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
meta import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
meta import VerifiedGarbage.Proof.TripleDes.AArch64.RoundFunction
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Store
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Tail
meta import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Word
meta import VerifiedGarbage.Proof.TripleDes.Bytes
meta import VerifiedGarbage.Proof.TripleDes.Permutation
meta import VerifiedGarbage.Proof.TripleDes.Round
meta import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.TripleDes.Word
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# Triple DES-CBC on AArch64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.AArch64.cbcEncryptChained_wp` and
`cbcDecryptChained_wp`) over Triple DES's core for each direction
(`dirCoreSpec`, calling the block function), with the feedback modes'
precondition (`fbPre`, as the IV is written too); encryption keeps the IV's
address in `x25`, which the core keeps (`keeps_x25`), as those modes do.
`cbcEncryptChained_verified`, `cbcDecryptChained_verified`: each is correct
and constant time, by the taint analysis with public values in vector
registers (`VectorTaint`) and the block functions' summaries (`encSum`,
`decSum`): the pointers, `n` and the stack pointer are public, and so is
everything the code computes from them; the IV is secret.
`cbcEncryptChained_framed` and `cbcDecryptChained_framed` run them with
their working space on the stack, zeroed on return: 1008 bytes, the 125
words of the scratch buffer and 8 more.
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

/-- CBC encryption on AArch64 that updates the chaining value. -/
def cbcEncAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

/-- The core's cipher is the contract's. -/
theorem invCipher_eq (k : Spec.TripleDes.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.TripleDes.invCipher k := rfl

/-! ## Decryption -/

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

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 125⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncryptChained_wp (dirCoreSpec .encrypt) (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩ keeps_x25)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one] at hdata hiv
  refine ⟨?_, ?_⟩
  · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
  · change _ = Spec.Cbc.next _ (Spec.Cbc.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _))
    rw [cbcBlocksAt_eq]; exact hiv

theorem cbcEncryptChained_verified :
    Verified AArch64.target cbcEncryptChained (Proof.TripleDes.cbcEncChainedScratchContract AArch64.abi 125) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcEncryptChained_keeps_x30 (cbcEncryptChained_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun s₁ s₂ h₁ h₂ hp => ⟨fbTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
        simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide_sum [encSum])) (by
    sig_implies [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, cbcEncAArch64, fbPre, fbPub, AArch64.abi,
      AArch64.argRegs] [fbSat] using fbSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.TripleDes.cbcEncryptChainedContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cbcEncryptChainedContract, Spec.TripleDes.cbcChainedSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cbcEncryptChained)
      (Spec.TripleDes.cbcEncryptChainedContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cbcEncChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cbcEncryptChained_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.TripleDes.AArch64
