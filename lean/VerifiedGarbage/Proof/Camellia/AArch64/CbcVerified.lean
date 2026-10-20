module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
import VerifiedGarbage.Proof.Camellia.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
public import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
public import VerifiedGarbage.Impl.Camellia.AArch64.Cbc
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Camellia.AArch64.Link
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Camellia.AArch64.Lit
meta import VerifiedGarbage.Impl.Camellia.AArch64.Cbc
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Camellia-CBC on AArch64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.AArch64.cbcEncryptChained_wp` and
`cbcDecryptChained_wp`) over Camellia's core for each direction: decryption over
`dirCoreSpec .decrypt`, encryption over the feedback modes' core
(`fbCoreSpec`), with the IV's address in `x19`, which the core keeps. The IV
is read and written, as for OFB and CFB, whose precondition and public
arguments these share (`fbPre`, `fbPub`). Each is correct and constant time,
by the taint analysis: the pointers, `n` (and any number of rounds) and the
stack pointer are public, and so is everything the code computes from them;
the IV is secret. The `_framed` theorems run them with their working space
on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Proof.Camellia (schedWords)

abbrev invCiphOf (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)

/-- CBC decryption on AArch64 that updates the chaining value. -/
def cbcDecAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cbc.decrypt (invCiphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on AArch64 that updates the chaining value. -/
def cbcEncAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

attribute [local irreducible] Spec.Camellia.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    ((dirCoreSpec .decrypt).toBlock rfl).cipher (R, schedWords m p R) = Spec.Camellia.invCipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem cbcTaint_agree (s₁ s₂ : State) (_ : fbPre s₁) (_ : fbPre s₂)
    (hp : fbPub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## Decryption -/

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecryptChained_wp ((dirCoreSpec .decrypt).toBlock rfl) (r := ⟨.x2, .x3, .x4, .x5⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := ((s₀.gpr .x1).toNat, schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKV⟩)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [invCipher_eq] at hdata
  exact ⟨hdata, hiv⟩

theorem cbcDecryptChained_ct : ConstantTime isa cbcDecAArch64.pre cbcDecAArch64.pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (fun s₁ s₂ h₁ h₂ hp => ⟨cbcTaint_agree s₁ s₂ h₁ h₂ hp, fun v hv => by
      simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hv⟩) (by taint_decide)

theorem cbcDecryptChained_correct (s : State) (hs : cbcDecAArch64.pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ cbcDecAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcDecryptChained_keeps_x30 (cbcDecryptChained_wp hs)
  exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained (Proof.Camellia.cbcDecChainedScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct cbcDecryptChained_correct cbcDecryptChained_ct (by
    sig_implies [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig,
      Proof.Camellia.cbcChainedPre, Proof.Camellia.cbcDecChainedPost, cbcDecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs, slots,
      tailSlot, savedSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cbcDecFrameSat_pre : ∃ s, (Spec.Camellia.cbcDecryptChainedContract AArch64.abi 3344).pre s := by
  implies_sat [Spec.Camellia.cbcDecryptChainedContract, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre,
    Proof.Camellia.cbcDecChainedPost, AArch64.abi, AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 cbcDecryptChained)
      (Spec.Camellia.cbcDecryptChainedContract AArch64.abi 3344) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 418) (pre := Proof.Camellia.cbcChainedPre AArch64.abi.ptrBits)
    (post := Proof.Camellia.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3344) (by rw [← Proof.Camellia.cbcDecChainedScratchContract_eq]; exact cbcDecryptChained_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-! ## Encryption -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncryptChained_wp fbCoreSpec (r := ⟨.x2, .x3, .x4, .x5⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := ((s₀.gpr .x1).toNat, schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKD⟩ keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [fbCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cbcEncryptChained_verified :
    Verified AArch64.target cbcEncryptChained (Proof.Camellia.cbcEncChainedScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cbcEncryptChained_keeps_x30 (cbcEncryptChained_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig,
      Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Proof.Camellia.cbcEncChainedPost, cbcEncAArch64, fbPre, fbPub,
      AArch64.abi, AArch64.argRegs, slots, tailSlot, savedSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Camellia.cbcEncryptChainedContract AArch64.abi 3344).pre s := by
  implies_sat [Spec.Camellia.cbcEncryptChainedContract, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre,
    Proof.Camellia.cbcEncChainedPost, AArch64.abi, AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- CFB128 encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 cbcEncryptChained)
      (Spec.Camellia.cbcEncryptChainedContract AArch64.abi 3344) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 418) (pre := Proof.Camellia.cbcChainedPre AArch64.abi.ptrBits)
    (post := Proof.Camellia.cbcEncChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3344) (by rw [← Proof.Camellia.cbcEncChainedScratchContract_eq]; exact cbcEncryptChained_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Camellia.AArch64
