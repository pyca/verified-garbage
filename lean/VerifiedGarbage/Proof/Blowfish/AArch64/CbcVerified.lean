module

public import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.CbcDecrypt
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncrypt
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncrypt
public import VerifiedGarbage.Proof.Blowfish.CbcScratch
meta import VerifiedGarbage.Proof.Blowfish.CbcScratch
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Blowfish-CBC on AArch64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over Blowfish's core (`Proof.Modes.AArch64.cbcEncrypt_wp` and `cbcDecrypt_wp`
with `dirCoreSpec`), in the two directions. The low halves of `v8`–`v15`
are kept because the modes' code writes no vector register and every run of
`crypt` keeps them (`vKeep_of_vSafeBut`, `crypt_vKeep`).
`cbcEncrypt_verified`, `cbcDecrypt_verified`: each is correct and constant
time, by the taint analysis: the pointers, `n` and the stack pointer are
public, and so is everything the code computes from them, which it keeps in
registers; the IV is secret. `cbcEncrypt_framed` and `cbcDecrypt_framed` run
them with their working space on the stack, zeroed on return: 224 bytes, the
28 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Blowfish

open VG VG.AArch64 VG.Impl.Blowfish.AArch64

/-- CBC decryption on AArch64 with its working space at `x4`. -/
def cbcDecAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 4168⟩
    let iv : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * 28⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .x0).toNat + 4168 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 28 ≤ 2 ^ 64
  post s s' :=
    Spec.Blowfish.cbcBlocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.decrypt (Spec.Blowfish.invCipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .x0)))
        (Spec.Aes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.Blowfish.cbcBlocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- CBC encryption on AArch64 with its working space at `x4`: as decryption,
with encryption's result. -/
def cbcEncAArch64 : Contract AArch64.isa where
  pre := cbcDecAArch64.pre
  post s s' :=
    Spec.Blowfish.cbcBlocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      Spec.Cbc.encrypt (Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .x0)))
        (Spec.Aes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.Blowfish.cbcBlocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub := cbcDecAArch64.pub

end VG.Proof.Blowfish

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.Impl.Blowfish.AArch64
open VG.Proof.Blowfish (cbcDecAArch64 cbcEncAArch64)

theorem cbcTaint_agree (s₁ s₂ : State) (_ : cbcDecAArch64.pre s₁) (_ : cbcDecAArch64.pre s₂)
    (hp : cbcDecAArch64.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The schedule, from the precondition: readable, and apart from the
writable regions. -/
theorem cbc_keyArgs {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    ModeKeyArgs s₀ [⟨s₀.gpr .x4, 8 * 28⟩] (Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .x0)) := by
  obtain ⟨hrd, hwr, dKD, dKS, -, -, -, fitK, -⟩ := hp
  refine ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => ?_⟩, fun r hr => ?_⟩
  · rw [hwr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact dKD
    · exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; exact dKS

/-- A state satisfying the precondition (one block). -/
def cbcSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x4000 | .x3 => 1 | .x4 => 0x5000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩, ⟨0x3000, 8⟩]
  wr := [⟨0x4000, 8⟩, ⟨0x5000, 8 * 28⟩]

/-- A state satisfying `vg_blowfish_cbc_encrypt`'s and
`vg_blowfish_cbc_decrypt`'s precondition: the schedule at `0x1000`, the IV
at `0x3000`, one block at `0x4000`. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x4000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩, ⟨0x3000, 8⟩]
  wr := [⟨0x4000, 8⟩]

/-! ## Decryption -/

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  have hk := cbc_keyArgs hp
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcDecrypt_wp (dirCoreSpec false) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD hk) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one] at hdata
  change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
  rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

/-- Every instruction keeps `v8`–`v15`, but in `crypt`. -/
theorem cbcDecrypt_vSafe : VSafeBut (dirCore false).crypt cbcDecrypt := by
  unfold cbcDecrypt; vsafe_but

theorem cbcDecrypt_ct : ConstantTime isa cbcDecAArch64.pre cbcDecAArch64.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcDecrypt_correct (s : State) (hs : cbcDecAArch64.pre s) :
    ∃ t s', Exec isa cbcDecrypt s t s' ∧ abiPreserved s s' ∧ cbcDecAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcDecrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he,
    vKeep_of_vSafeBut cbcDecrypt_vSafe (crypt_vKeep false) _ _ _ he⟩, h₂⟩

theorem cbcDecrypt_verified :
    Verified AArch64.target cbcDecrypt (Proof.Blowfish.cbcDecScratchContract AArch64.abi 28) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.Blowfish.cbcDecScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig,
      Proof.Blowfish.cbcDecPost, cbcDecAArch64, AArch64.abi, AArch64.argRegs] [cbcSat] using cbcSat)

theorem cbcFrameSat_pre : ∃ s, (Spec.Blowfish.cbcDecryptContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cbcDecryptContract, Spec.Blowfish.cbcSig, AArch64.abi, AArch64.argRegs]
    [cbcFrameSat] using cbcFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cbcDecrypt)
      (Spec.Blowfish.cbcDecryptContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Blowfish.cbcDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cbcDecrypt_verified
    (by decide) (by decide) (by decide) (Proof.Blowfish.cbcDecPostOut_local _) cbcFrameSat_pre

/-! ## Encryption -/

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncAArch64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcEncAArch64.post s₀ s' := by
  have hk := cbc_keyArgs hp
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain ⟨p, hp, hK, hS, -⟩ := hk
  refine WP.mono (Proof.Modes.AArch64.cbcEncrypt_wp (dirCoreSpec true) (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨p, hp, hK, hS, fun r hr => by
      subst hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [dirCore_bw, Nat.mul_one] at hdata
  change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
  rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

/-- Every instruction keeps `v8`–`v15`, but in `crypt`. -/
theorem cbcEncrypt_vSafe : VSafeBut (dirCore true).crypt cbcEncrypt := by
  unfold cbcEncrypt; vsafe_but

theorem cbcEncrypt_ct : ConstantTime isa cbcEncAArch64.pre cbcEncAArch64.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) cbcTaint_agree (by taint_decide)

theorem cbcEncrypt_correct (s : State) (hs : cbcEncAArch64.pre s) :
    ∃ t s', Exec isa cbcEncrypt s t s' ∧ abiPreserved s s' ∧ cbcEncAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cbcEncrypt_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨Proof.Modes.AArch64.preserved_of h₁ h₃, Exec.sp he,
    vKeep_of_vSafeBut cbcEncrypt_vSafe (crypt_vKeep true) _ _ _ he⟩, h₂⟩

theorem cbcEncrypt_verified :
    Verified AArch64.target cbcEncrypt (Proof.Blowfish.cbcEncScratchContract AArch64.abi 28) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.Blowfish.cbcEncScratchContract, Proof.Blowfish.cbcScratchSig, Spec.Blowfish.cbcSig,
      Proof.Blowfish.cbcEncPost, cbcEncAArch64, cbcDecAArch64, AArch64.abi, AArch64.argRegs] [cbcSat]
      using cbcSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Blowfish.cbcEncryptContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cbcEncryptContract, Spec.Blowfish.cbcSig, AArch64.abi, AArch64.argRegs]
    [cbcFrameSat] using cbcFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cbcEncrypt)
      (Spec.Blowfish.cbcEncryptContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Blowfish.cbcEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cbcEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.Blowfish.cbcEncPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Blowfish.AArch64
