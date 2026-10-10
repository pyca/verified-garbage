import VerifiedGarbage.Proof.Sm4.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncrypt
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm4.AArch64.Lit

/-!
# SM4-CBC on AArch64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over SM4's core for each direction (`Proof.Modes.AArch64.cbcEncrypt_wp` and
`cbcDecrypt_wp` with `dirCoreSpec`). `cbcEncrypt_verified`,
`cbcDecrypt_verified`: each is correct and constant time, by the taint
analysis: the pointers, `n` and the stack pointer are public, and so is
everything the code computes from them, which it keeps in registers; the IV
is secret. `cbcEncrypt_framed` and `cbcDecrypt_framed` run them with their
working space on the stack, zeroed on return: 3168 bytes, the 396 words of
the scratch buffer.
-/

namespace VG.Proof.Sm4

open VG VG.AArch64 VG.Impl.Sm4.AArch64

/-- CBC decryption on AArch64 with its working space at `x4`. -/
def cbcDecAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let iv : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * slots⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.decrypt (Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)))
        (Spec.Aes.bytesAt s.mem (s.gpr .x1) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- CBC encryption on AArch64 with its working space at `x4`: as decryption,
with encryption's result. -/
def cbcEncAArch64 : Contract AArch64.isa where
  pre := cbcDecAArch64.pre
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.encrypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)))
        (Spec.Aes.bytesAt s.mem (s.gpr .x1) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub := cbcDecAArch64.pub

end VG.Proof.Sm4

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64
open VG.Proof.Sm4 (cbcDecAArch64 cbcEncAArch64)

attribute [local irreducible] Spec.Sm4.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (k : Spec.Sm4.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.Sm4.invCipher k := rfl

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem encCipher_eq (k : Spec.Sm4.Schedule) : (dirCoreSpec .encrypt).cipher k = Spec.Sm4.cipher k := rfl

/-- The callee-saved registers the modes keep, and the link register. -/
theorem preserved_of {s s' : State} (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
    s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

theorem cbcTaint_agree (s₁ s₂ : State) (_ : cbcDecAArch64.pre s₁) (_ : cbcDecAArch64.pre s₂)
    (hp : cbcDecAArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def cbcSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 396⟩]

/-- A state satisfying `vg_sm4_cbc_encrypt`'s and `vg_sm4_cbc_decrypt`'s
precondition: the schedule at `0x1000`, the IV at `0x2000`, one block at
`0x3000`. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 16⟩]

/-! ## Decryption -/

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecrypt_wp (dirCoreSpec .decrypt) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [invCipher_eq] at hdata
  exact hdata

theorem cbcDecrypt_ct : ConstantTime isa cbcDecAArch64.pre cbcDecAArch64.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcDecrypt_correct (s : State) (hs : cbcDecAArch64.pre s) :
    ∃ t s', Exec isa cbcDecrypt s t s' ∧ abiPreserved s s' ∧ cbcDecAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcDecrypt_verified :
    Verified AArch64.target cbcDecrypt (Proof.Sm4.cbcDecScratchContract AArch64.abi slots) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost,
      cbcDecAArch64, AArch64.abi, AArch64.argRegs, slots, tableEnd, tableSlot] [cbcSat] using cbcSat)

theorem cbcFrameSat_pre : ∃ s, (Spec.Sm4.cbcDecryptContract AArch64.abi 3168).pre s := by
  implies_sat [Spec.Sm4.cbcDecryptContract, Spec.Sm4.cbcSig, AArch64.abi, AArch64.argRegs] [cbcFrameSat]
    using cbcFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 cbcDecrypt)
      (Spec.Sm4.cbcDecryptContract AArch64.abi 3168) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64)
    (n := 396) (post := Proof.Sm4.cbcDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3168) cbcDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cbcDecPostOut_local _) cbcFrameSat_pre

/-! ## Encryption -/

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncrypt_wp (dirCoreSpec .encrypt) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [encCipher_eq] at hdata
  exact hdata

theorem cbcEncrypt_ct : ConstantTime isa cbcEncAArch64.pre cbcEncAArch64.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcEncrypt_correct (s : State) (hs : cbcEncAArch64.pre s) :
    ∃ t s', Exec isa cbcEncrypt s t s' ∧ abiPreserved s s' ∧ cbcEncAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcEncrypt_verified :
    Verified AArch64.target cbcEncrypt (Proof.Sm4.cbcEncScratchContract AArch64.abi slots) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost,
      cbcEncAArch64, cbcDecAArch64, AArch64.abi, AArch64.argRegs, slots, tableEnd, tableSlot] [cbcSat]
      using cbcSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Sm4.cbcEncryptContract AArch64.abi 3168).pre s := by
  implies_sat [Spec.Sm4.cbcEncryptContract, Spec.Sm4.cbcSig, AArch64.abi, AArch64.argRegs] [cbcFrameSat]
    using cbcFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 cbcEncrypt)
      (Spec.Sm4.cbcEncryptContract AArch64.abi 3168) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64)
    (n := 396) (post := Proof.Sm4.cbcEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3168) cbcEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cbcEncPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Sm4.AArch64
