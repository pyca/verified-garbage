module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
public import VerifiedGarbage.Proof.Blowfish.CbcScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.Blowfish.CbcScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Data.List.Induction
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import Mathlib.Data.List.Induction
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Blowfish-CBC on AArch64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.AArch64.cbcEncryptChained_wp` and
`cbcDecryptChained_wp`) over Blowfish's core in the two directions
(`dirCoreSpec`), with the feedback modes' precondition (`fbPre`, as the IV is
written too); encryption keeps the IV's address in `x25`, which the core
keeps (`crypt_keeps`), as those modes do. `cbcEncryptChained_verified`,
`cbcDecryptChained_verified`: each is correct and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them; the IV is secret. The batch
writes `v8`–`v15`, which `crypt` keeps (`vKeep_of_vSafeBut`, `crypt_vKeep`).
`cbcEncryptChained_framed` and `cbcDecryptChained_framed` run them with
their working space on the stack, zeroed on return: 224 bytes, the 28 words
of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.Impl.Blowfish.AArch64

/-- CBC decryption on AArch64 that updates the chaining value. -/
def cbcDecAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.Blowfish.invCipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .x0))) (ivOf s)
        (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on AArch64 that updates the chaining value. -/
def cbcEncAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

/-! ## Decryption -/

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp (dirCoreSpec false) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
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
      · exact dKV⟩) fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one] at hdata hiv
  refine ⟨?_, ?_⟩
  · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
  · change _ = Spec.Cbc.next _ (Spec.Blowfish.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq]; exact hiv

/-- Every instruction keeps `v8`–`v15`, but in `crypt`. -/
theorem cbcDecryptChained_vSafe : VSafeBut (dirCore false).crypt cbcDecryptChained := by
  unfold cbcDecryptChained; vsafe_but

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained (Proof.Blowfish.cbcDecChainedScratchContract AArch64.abi 28) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecryptChained_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he,
        vKeep_of_vSafeBut cbcDecryptChained_vSafe (crypt_vKeep false) _ _ _ he⟩, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig,
      Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, cbcDecAArch64, fbPre, fbPub, AArch64.abi,
      AArch64.argRegs] [fbSat] using fbSat)

theorem cbcDecFrameSat_pre : ∃ s, (Spec.Blowfish.cbcDecryptChainedContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cbcDecryptChainedContract, Spec.Blowfish.cbcChainedSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cbcDecryptChained)
      (Spec.Blowfish.cbcDecryptChainedContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Blowfish.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cbcDecryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Blowfish.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-! ## Encryption -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncryptChained_wp (dirCoreSpec true) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
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
      · exact dKD⟩ crypt_keeps)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one] at hdata hiv
  refine ⟨?_, ?_⟩
  · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
  · change _ = Spec.Cbc.next _ (Spec.Cbc.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _))
    rw [cbcBlocksAt_eq]; exact hiv

/-- Every instruction keeps `v8`–`v15`, but in `crypt`. -/
theorem cbcEncryptChained_vSafe : VSafeBut (dirCore true).crypt cbcEncryptChained := by
  unfold cbcEncryptChained; vsafe_but

theorem cbcEncryptChained_verified :
    Verified AArch64.target cbcEncryptChained (Proof.Blowfish.cbcEncChainedScratchContract AArch64.abi 28) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncryptChained_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he,
        vKeep_of_vSafeBut cbcEncryptChained_vSafe (crypt_vKeep true) _ _ _ he⟩, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig,
      Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, cbcEncAArch64, fbPre, fbPub, AArch64.abi,
      AArch64.argRegs] [fbSat] using fbSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Blowfish.cbcEncryptChainedContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cbcEncryptChainedContract, Spec.Blowfish.cbcChainedSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cbcEncryptChained)
      (Spec.Blowfish.cbcEncryptChainedContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Blowfish.cbcEncChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cbcEncryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Blowfish.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Blowfish.AArch64
