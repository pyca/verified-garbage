module

import VerifiedGarbage.Proof.Sm4.AArch64.Link
meta import VerifiedGarbage.Proof.Sm4.AArch64.Link
public import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
meta import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
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
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Counter
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Unchain
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Sm4.AArch64.Copy
import VerifiedGarbage.Proof.Sm4.AArch64.Crypt16
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.Planes
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
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.AArch64.Copy
meta import VerifiedGarbage.Proof.Modes.AArch64.Counter
meta import VerifiedGarbage.Proof.Modes.AArch64.Ctr
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Unchain
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.CbcNext
meta import VerifiedGarbage.Proof.Sm4.AArch64.Copy
meta import VerifiedGarbage.Proof.Sm4.AArch64.Crypt16
meta import VerifiedGarbage.Proof.Sm4.AArch64.Imm
meta import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# SM4-CBC on AArch64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.AArch64.cbcEncryptChained_wp` and
`cbcDecryptChained_wp`) over SM4's core for each direction: decryption over
`dirCoreSpec .decrypt`, encryption over the feedback modes' core
(`fbCoreSpec`), with the IV's address in `x19`, which the core keeps in
`v31` (`keeps_x19`). `cbcEncryptChained_verified`,
`cbcDecryptChained_verified`: each is correct and constant time, by the
taint analysis with public values in vector registers (`VectorTaint`), as
for OFB and CFB (`fbPre`, `fbTaint_agree`): the pointers, `n` and the stack
pointer are public, and so is everything the code computes from them, which
it keeps in registers; the IV is secret. `cbcEncryptChained_framed` and
`cbcDecryptChained_framed` run them with their working space on the stack,
zeroed on return: 3264 bytes, the 408 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64

/-- CBC decryption on AArch64 that updates the chaining value. -/
def cbcDecAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0))) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on AArch64 that updates the chaining value. -/
def cbcEncAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

attribute [local irreducible] Spec.Sm4.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (k : Spec.Sm4.Schedule) : ((dirCoreSpec .decrypt).toBlock rfl).cipher k = Spec.Sm4.invCipher k := rfl

/-! ## Decryption -/

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp ((dirCoreSpec .decrypt).toBlock rfl)
    (r := ⟨.x1, .x2, .x3, .x4⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩) fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [invCipher_eq] at hdata
  exact ⟨hdata, hiv⟩

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained (Proof.Sm4.cbcDecChainedScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcDecryptChained_keeps_x30 (cbcDecryptChained_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide_sum [cryptSum])) (by
    sig_implies [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Proof.Sm4.cbcDecChainedPost, cbcDecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs, slots, tableEnd,
      tableSlot] [fbSat] using fbSat)

theorem cbcDecFrameSat_pre : ∃ s, (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 3264).pre s := by
  implies_sat [Spec.Sm4.cbcDecryptChainedContract, Spec.Sm4.cbcChainedSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 cbcDecryptChained)
      (Spec.Sm4.cbcDecryptChainedContract AArch64.abi 3264) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) cbcDecryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-! ## Encryption -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncryptChained_wp fbCoreSpec (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩ keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [fbCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cbcEncryptChained_verified :
    Verified AArch64.target cbcEncryptChained (Proof.Sm4.cbcEncChainedScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcEncryptChained_keeps_x30 (cbcEncryptChained_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide_sum [cryptSum])) (by
    sig_implies [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Proof.Sm4.cbcEncChainedPost, cbcEncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs, slots, tableEnd,
      tableSlot] [fbSat] using fbSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 3264).pre s := by
  implies_sat [Spec.Sm4.cbcEncryptChainedContract, Spec.Sm4.cbcChainedSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 cbcEncryptChained)
      (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 3264) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.cbcEncChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) cbcEncryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Sm4.AArch64
