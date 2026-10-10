import VerifiedGarbage.Proof.TripleDes.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncrypt
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Triple DES-CBC on AArch64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over Triple DES's core for each direction (`Proof.Modes.AArch64.cbcEncrypt_wp`
and `cbcDecrypt_wp` with `dirCoreSpec`). `cbcEncrypt_verified`,
`cbcDecrypt_verified`: each is correct and constant time, by the taint
analysis: the pointers, `n` and the stack pointer are public, and so is
everything the code computes from them, which it keeps in registers; the IV
is secret. `cbcEncrypt_framed` and `cbcDecrypt_framed` run them with their
working space on the stack, zeroed on return: 1008 bytes, the 125 words of
the scratch buffer rounded up to the stack's alignment.
-/

namespace VG.Proof.TripleDes

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- CBC decryption on AArch64 with its working space at `x4`. -/
def cbcDecAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 384⟩
    let iv : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * 125⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 125 ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.cbcBlocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.decrypt (Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)))
        (Spec.TripleDes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.TripleDes.cbcBlocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- CBC encryption on AArch64 with its working space at `x4`: as decryption,
with encryption's result. -/
def cbcEncAArch64 : Contract AArch64.isa where
  pre := cbcDecAArch64.pre
  post s s' :=
    Spec.TripleDes.cbcBlocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.encrypt (Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)))
        (Spec.TripleDes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.TripleDes.cbcBlocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub := cbcDecAArch64.pub

end VG.Proof.TripleDes

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Proof.TripleDes (cbcDecAArch64 cbcEncAArch64)

/-- The core's cipher is the contract's. -/
theorem invCipher_eq (k : Spec.TripleDes.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.TripleDes.invCipher k := rfl

/-- The core's cipher is the contract's. -/
theorem encCipher_eq (k : Spec.TripleDes.Schedule) : (dirCoreSpec .encrypt).cipher k = Spec.TripleDes.cipher k := rfl

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
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 8 * 125⟩]

/-- A state satisfying `vg_triple_des_cbc_encrypt`'s and
`vg_triple_des_cbc_decrypt`'s precondition: the schedule at `0x1000`, the IV
at `0x2000`, one block at `0x3000`. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 8⟩]

/-! ## Decryption -/

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 125⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecrypt_wp (dirCoreSpec .decrypt) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one, invCipher_eq] at hdata
  change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
  rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

theorem cbcDecrypt_ct : ConstantTime isa cbcDecAArch64.pre cbcDecAArch64.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcDecrypt_correct (s : State) (hs : cbcDecAArch64.pre s) :
    ∃ t s', Exec isa cbcDecrypt s t s' ∧ abiPreserved s s' ∧ cbcDecAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcDecrypt_verified :
    Verified AArch64.target cbcDecrypt (Proof.TripleDes.cbcDecScratchContract AArch64.abi 125) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig,
      Proof.TripleDes.cbcDecPost, cbcDecAArch64, AArch64.abi, AArch64.argRegs] [cbcSat] using cbcSat)

theorem cbcFrameSat_pre : ∃ s, (Spec.TripleDes.cbcDecryptContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cbcDecryptContract, Spec.TripleDes.cbcSig, AArch64.abi, AArch64.argRegs]
    [cbcFrameSat] using cbcFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cbcDecrypt)
      (Spec.TripleDes.cbcDecryptContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cbcDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cbcDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cbcDecPostOut_local _) cbcFrameSat_pre

/-! ## Encryption -/

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 125⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncrypt_wp (dirCoreSpec .encrypt) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one, encCipher_eq] at hdata
  change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
  rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

theorem cbcEncrypt_ct : ConstantTime isa cbcEncAArch64.pre cbcEncAArch64.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcEncrypt_correct (s : State) (hs : cbcEncAArch64.pre s) :
    ∃ t s', Exec isa cbcEncrypt s t s' ∧ abiPreserved s s' ∧ cbcEncAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem cbcEncrypt_verified :
    Verified AArch64.target cbcEncrypt (Proof.TripleDes.cbcEncScratchContract AArch64.abi 125) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig,
      Proof.TripleDes.cbcEncPost, cbcEncAArch64, cbcDecAArch64, AArch64.abi, AArch64.argRegs] [cbcSat]
      using cbcSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.TripleDes.cbcEncryptContract AArch64.abi 1008).pre s := by
  implies_sat [Spec.TripleDes.cbcEncryptContract, Spec.TripleDes.cbcSig, AArch64.abi, AArch64.argRegs]
    [cbcFrameSat] using cbcFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1008 .x4 125 cbcEncrypt)
      (Spec.TripleDes.cbcEncryptContract AArch64.abi 1008) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64)
    (n := 125) (post := Proof.TripleDes.cbcEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1008) cbcEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cbcEncPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.TripleDes.AArch64
