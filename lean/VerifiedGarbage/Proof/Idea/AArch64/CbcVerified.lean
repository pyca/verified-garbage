import VerifiedGarbage.Proof.Idea.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncrypt
import VerifiedGarbage.Proof.Idea.CbcScratch
import VerifiedGarbage.Proof.Idea.AArch64.ModesLit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# IDEA-CBC on AArch64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over IDEA's core (`Proof.Modes.AArch64.cbcEncrypt_wp` and `cbcDecrypt_wp`
with `modeCoreSpec`), under the encryption and the decryption subkeys.
`cbcEncrypt_verified`, `cbcDecrypt_verified`: each is correct and constant
time, by the taint analysis: the pointers, `n` and the stack pointer are
public, and so is everything the code computes from them, which it keeps in
registers; the IV is secret. `cbcEncrypt_framed` and `cbcDecrypt_framed` run
them with their working space on the stack, zeroed on return: 208 bytes, the
26 words of the scratch buffer.
-/

namespace VG.Proof.Idea

open VG VG.AArch64 VG.Impl.Idea.AArch64

/-- CBC decryption on AArch64 with its working space at `x4`. -/
def cbcDecAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 104⟩
    let iv : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * 26⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 104 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 26 ≤ 2 ^ 64
  post s s' :=
    Spec.Idea.cbcBlocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.decrypt (Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .x0)))
        (Spec.Aes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.Idea.cbcBlocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- CBC encryption on AArch64 with its working space at `x4`: as decryption,
with encryption's result. -/
def cbcEncAArch64 : Contract AArch64.isa where
  pre := cbcDecAArch64.pre
  post s s' :=
    Spec.Idea.cbcBlocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.encrypt (Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .x0)))
        (Spec.Aes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.Idea.cbcBlocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub := cbcDecAArch64.pub

end VG.Proof.Idea

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64
open VG.Proof.Idea (cbcDecAArch64 cbcEncAArch64)

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
  rd := [⟨0x1000, 104⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 8 * 26⟩]

/-- A state satisfying `vg_idea_cbc_encrypt`'s and `vg_idea_cbc_decrypt`'s
precondition: the schedule at `0x1000`, the IV at `0x2000`, one block at
`0x3000`. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 104⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 8⟩]

/-! ## Decryption -/

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 26⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecrypt_wp modeCoreSpec (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Idea.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [modeCore_bw, Nat.mul_one] at hdata
  change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
  rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

theorem cbcDecrypt_ct : ConstantTime isa cbcDecAArch64.pre cbcDecAArch64.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcDecrypt_correct (s : State) (hs : cbcDecAArch64.pre s) :
    ∃ t s', Exec isa cbcDecrypt s t s' ∧ abiPreserved s s' ∧ cbcDecAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcDecrypt_verified :
    Verified AArch64.target cbcDecrypt (Proof.Idea.cbcDecScratchContract AArch64.abi 26) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.Idea.cbcDecScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig,
      Proof.Idea.cbcDecPost, cbcDecAArch64, AArch64.abi, AArch64.argRegs] [cbcSat] using cbcSat)

theorem cbcFrameSat_pre : ∃ s, (Spec.Idea.cbcDecryptContract AArch64.abi 208).pre s := by
  implies_sat [Spec.Idea.cbcDecryptContract, Spec.Idea.cbcSig, AArch64.abi, AArch64.argRegs]
    [cbcFrameSat] using cbcFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 cbcDecrypt)
      (Spec.Idea.cbcDecryptContract AArch64.abi 208) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Idea.cbcSig) (nm := "scratch") (e := .u64)
    (n := 26) (post := Proof.Idea.cbcDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cbcDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Idea.cbcDecPostOut_local _) cbcFrameSat_pre

/-! ## Encryption -/

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 26⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncrypt_wp modeCoreSpec (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Idea.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [modeCore_bw, Nat.mul_one] at hdata
  change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
  rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

theorem cbcEncrypt_ct : ConstantTime isa cbcEncAArch64.pre cbcEncAArch64.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcEncrypt_correct (s : State) (hs : cbcEncAArch64.pre s) :
    ∃ t s', Exec isa cbcEncrypt s t s' ∧ abiPreserved s s' ∧ cbcEncAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcEncrypt_verified :
    Verified AArch64.target cbcEncrypt (Proof.Idea.cbcEncScratchContract AArch64.abi 26) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.Idea.cbcEncScratchContract, Proof.Idea.cbcScratchSig, Spec.Idea.cbcSig,
      Proof.Idea.cbcEncPost, cbcEncAArch64, cbcDecAArch64, AArch64.abi, AArch64.argRegs] [cbcSat]
      using cbcSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Idea.cbcEncryptContract AArch64.abi 208).pre s := by
  implies_sat [Spec.Idea.cbcEncryptContract, Spec.Idea.cbcSig, AArch64.abi, AArch64.argRegs]
    [cbcFrameSat] using cbcFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 208 .x4 26 cbcEncrypt)
      (Spec.Idea.cbcEncryptContract AArch64.abi 208) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Idea.cbcSig) (nm := "scratch") (e := .u64)
    (n := 26) (post := Proof.Idea.cbcEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cbcEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.Idea.cbcEncPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Idea.AArch64
