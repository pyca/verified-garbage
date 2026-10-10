import VerifiedGarbage.Proof.Camellia.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncrypt
import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Camellia.AArch64.Lit

/-!
# Camellia-CBC on AArch64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over Camellia's core for each direction (`Proof.Modes.AArch64.cbcEncrypt_wp`
and `cbcDecrypt_wp` with `dirCoreSpec`). `cbcEncrypt_verified`,
`cbcDecrypt_verified`: each is correct and constant time, by the taint
analysis: the pointers, `rounds`, `n` and the stack pointer are public, and
so is everything the code computes from them, which it keeps in registers;
the IV is secret. `cbcEncrypt_framed` and `cbcDecrypt_framed` run them with
their working space on the stack, zeroed on return: 3248 bytes, the 406
words of the scratch buffer.
-/

namespace VG.Proof.Camellia

open VG VG.AArch64 VG.Impl.Camellia.AArch64

/-- CBC decryption on AArch64 with its working space at `x5`. -/
def cbcDecAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 272⟩
    let iv : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 8 * slots⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 8 * slots ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24)
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
      Spec.Cbc.decrypt (Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
        (Spec.Aes.bytesAt s.mem (s.gpr .x2) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- CBC encryption on AArch64 with its working space at `x5`: as decryption,
with encryption's result. -/
def cbcEncAArch64 : Contract AArch64.isa where
  pre := cbcDecAArch64.pre
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
      Spec.Cbc.encrypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .x0) (s.gpr .x1).toNat))
        (Spec.Aes.bytesAt s.mem (s.gpr .x2) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub := cbcDecAArch64.pub

end VG.Proof.Camellia

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Proof.Camellia (cbcDecAArch64 cbcEncAArch64 schedWords)

attribute [local irreducible] Spec.Camellia.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .decrypt).cipher (R, schedWords m p R) = Spec.Camellia.invCipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

attribute [local irreducible] Spec.Camellia.cipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem encCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .encrypt).cipher (R, schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

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
    (hp : cbcDecAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block, 18 rounds). -/
def cbcSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 406⟩]

/-- A state satisfying CBC's precondition: the schedule at `0x1000`, the
IV at `0x2000`, one block at `0x3000`, 18 rounds. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 16⟩]

/-! ## Decryption -/

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecrypt_wp (dirCoreSpec .decrypt) (r := ⟨.x2, .x3, .x4, .x5⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := ((s₀.gpr .x1).toNat, schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD
    ⟨s₀.gpr .x0, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩)
    fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [invCipher_eq] at hdata
  exact hdata

theorem cbcDecrypt_ct : ConstantTime isa cbcDecAArch64.pre cbcDecAArch64.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) cbcTaint_agree
    (by taint_decide)

theorem cbcDecrypt_correct (s : State) (hs : cbcDecAArch64.pre s) :
    ∃ t s', Exec isa cbcDecrypt s t s' ∧ abiPreserved s s' ∧ cbcDecAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcDecrypt_verified :
    Verified AArch64.target cbcDecrypt (Proof.Camellia.cbcDecScratchContract AArch64.abi slots) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig,
      Spec.Camellia.cbcPre, Spec.Camellia.cbcDecryptPost, cbcDecAArch64, AArch64.abi, AArch64.argRegs, slots,
      tailSlot, savedSlot, endSlot, keySlot] [cbcSat] using cbcSat)

theorem cbcFrameSat_pre : ∃ s, (Spec.Camellia.cbcDecryptContract AArch64.abi 3248).pre s := by
  implies_sat [Spec.Camellia.cbcDecryptContract, Spec.Camellia.cbcSig, Spec.Camellia.cbcPre,
    Spec.Camellia.cbcDecryptPost, AArch64.abi, AArch64.argRegs] [cbcFrameSat] using cbcFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 cbcDecrypt)
      (Spec.Camellia.cbcDecryptContract AArch64.abi 3248) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcSig) (nm := "scratch") (e := .u64)
    (n := 406) (pre := Spec.Camellia.cbcPre AArch64.abi.ptrBits)
    (post := Spec.Camellia.cbcDecryptPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3248) (by rw [← Proof.Camellia.cbcDecScratchContract_eq]; exact cbcDecrypt_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.cbcDecPostOut_local _) cbcFrameSat_pre

/-! ## Encryption -/

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncrypt_wp (dirCoreSpec .encrypt) (r := ⟨.x2, .x3, .x4, .x5⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := ((s₀.gpr .x1).toNat, schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKD⟩)
    fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [encCipher_eq] at hdata
  exact hdata

theorem cbcEncrypt_ct : ConstantTime isa cbcEncAArch64.pre cbcEncAArch64.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) cbcTaint_agree
    (by taint_decide)

theorem cbcEncrypt_correct (s : State) (hs : cbcEncAArch64.pre s) :
    ∃ t s', Exec isa cbcEncrypt s t s' ∧ abiPreserved s s' ∧ cbcEncAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcEncrypt_verified :
    Verified AArch64.target cbcEncrypt (Proof.Camellia.cbcEncScratchContract AArch64.abi slots) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig,
      Spec.Camellia.cbcPre, Spec.Camellia.cbcEncryptPost, cbcEncAArch64, cbcDecAArch64, AArch64.abi,
      AArch64.argRegs, slots, tailSlot, savedSlot, endSlot, keySlot] [cbcSat] using cbcSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Camellia.cbcEncryptContract AArch64.abi 3248).pre s := by
  implies_sat [Spec.Camellia.cbcEncryptContract, Spec.Camellia.cbcSig, Spec.Camellia.cbcPre,
    Spec.Camellia.cbcEncryptPost, AArch64.abi, AArch64.argRegs] [cbcFrameSat] using cbcFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3248 .x5 406 cbcEncrypt)
      (Spec.Camellia.cbcEncryptContract AArch64.abi 3248) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcSig) (nm := "scratch") (e := .u64)
    (n := 406) (pre := Spec.Camellia.cbcPre AArch64.abi.ptrBits)
    (post := Spec.Camellia.cbcEncryptPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3248) (by rw [← Proof.Camellia.cbcEncScratchContract_eq]; exact cbcEncrypt_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.cbcEncPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Camellia.AArch64
