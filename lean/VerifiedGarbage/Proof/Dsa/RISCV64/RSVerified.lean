module

import VerifiedGarbage.Proof.Dsa.RISCV64.RSCT
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedSignCT
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedImplies
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSImplies
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCall
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedSignFn
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Impl.Dsa.RISCV64.RandomSign
public import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Randomized DSA signing on RISC-V: verified against the shared contracts

The randomized signer's proofs are generic over the signer it calls
(`RS.Signer`). Over `vg_dsa_sign` (`fullSigner`), which checks the whole key,
it is `vg_dsa_sign_random` (`randomSign_verified`); over
`vg_dsa_sign_prevalidated` (`preSigner`), for a key that passes validation,
it is `vg_dsa_sign_random_prevalidated` (`randomSignPre_verified`), whose
contract `rspContract` adds validation to `rsContract`'s precondition
(`rsp_implies`). Both use `RS.rsStack` bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Dsa.RISCV64.RS

/-- `vg_dsa_sign`, for any key. -/
def fullSigner : Signer where
  name := "vg_dsa_sign"
  code := Sign.sign
  valid := fun _ _ _ => true
  correct := fun s h => sign_correct s h.1
  ct := fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => CT.sign_ct s₁ s₂ t₁ t₂ u₁ u₂ h₁.1 h₂.1
  noFrames := by decide +kernel

/-- `vg_dsa_sign_prevalidated`, for a key that passes validation. -/
def preSigner : Signer where
  name := "vg_dsa_sign_prevalidated"
  code := PrevalidatedSign.sign
  valid := Spec.Dsa.validatePrivateKeyBytes
  correct := signPre_correct
  ct := CT.signPre_ct
  noFrames := by decide +kernel

/-- `vg_dsa_sign_random`. -/
theorem randomSign_verified :
    Verified RISCV64.target RandomSign.code (Spec.Dsa.randomSignContract RISCV64.abi RS.rsStack) :=
  show Verified RISCV64.target (RandomSign.codeWith fullSigner.name fullSigner.code) _ from
  Verified.of_correct (k := rsContract) (fun s h => randomSignWith_correct fullSigner s h rfl)
    (fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => randomSignWith_ct fullSigner s₁ s₂ t₁ t₂ u₁ u₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩)
    randomSign_implies

/-- `vg_dsa_sign_random_prevalidated`, on the registers and the stack. -/
def rspContract : Contract isa where
  pre s := rsContract.pre s ∧ RandomValid preSigner s
  post := rsContract.post
  pub := rsContract.pub

theorem prev_pre {s : State} (h : (Spec.Dsa.randomSignPrevalidatedContract RISCV64.abi RS.rsStack).pre s) :
    (Spec.Dsa.randomSignContract RISCV64.abi RS.rsStack).pre s ∧
      Spec.Dsa.validatePrivateKeyBytes (s.gpr .a5).toNat (s.gpr .a6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) = true := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs,
    rsStackArgs_five, stackBelow] at h
  sig_split h
  refine ⟨?_, by with_reducible assumption⟩
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsStackArgs_five,
    stackBelow]
  sig_and_intros <;> with_reducible assumption

theorem prev_of_pre {s : State} (h : (Spec.Dsa.randomSignContract RISCV64.abi RS.rsStack).pre s)
    (hv : Spec.Dsa.validatePrivateKeyBytes (s.gpr .a5).toNat (s.gpr .a6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) = true) :
    (Spec.Dsa.randomSignPrevalidatedContract RISCV64.abi RS.rsStack).pre s := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsStackArgs_five,
    stackBelow] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs,
    rsStackArgs_five, stackBelow]
  sig_split h
  sig_and_intros <;> with_reducible assumption

/-- `rsSatState` with `validPrivateKeyWitness` at `0x1000`. -/
def rspSatState : State where
  gpr := rsSatState.gpr
  sp := rsSatState.sp
  mem a := if 0x1000 ≤ a.toNat ∧ a.toNat < 0x11a8 then
    VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x1000]?.getD 0 else rsSatState.mem a
  rd := rsSatState.rd
  wr := rsSatState.wr

theorem rspSat_key : Spec.Rsa.bytesAt rspSatState.mem 0x1000 424 = VG.Proof.Dsa.validPrivateKeyWitness :=
  bytesAt_window (base := 0x1000) VG.Proof.Dsa.validPrivateKeyWitness_length (by decide) fun a h₁ h₂ => by
    simp only [rspSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem rspSat_valid : Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt rspSatState.mem 0x1000 424) = true := by
  rw [rspSat_key]; exact VG.Proof.Dsa.validPrivateKeyWitness_valid

theorem rspSatisfiable : ∃ s, (Spec.Dsa.randomSignPrevalidatedContract RISCV64.abi RS.rsStack).pre s := by
  have ho : ∃ s, (Spec.Dsa.randomSignContract RISCV64.abi RS.rsStack).pre s ∧ s = rspSatState := by
    sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, RISCV64.abi, RISCV64.argRegs, rsContract,
      rsStackArgs_five, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      [rspSatState, rsSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rspSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, prev_of_pre h rspSat_valid⟩

theorem rsp_implies : rspContract.Implies (Spec.Dsa.randomSignPrevalidatedContract RISCV64.abi RS.rsStack) where
  pre s h := by
    obtain ⟨h₁, hv⟩ := prev_pre h
    have hr := randomSign_implies.pre s h₁
    refine ⟨hr, ?_⟩
    show Spec.Dsa.validatePrivateKeyBytes (rlOf s).pl (rlOf s).ql
      (Spec.Rsa.bytesAt s.mem (rlOf s).key (rlOf s).kl) = true
    rw [pre_kl hr]
    exact hv
  post s s' h hp := randomSign_implies.post s s' (prev_pre h).1 hp
  pub s₁ s₂ h₁ h₂ hp := randomSign_implies.pub s₁ s₂ (prev_pre h₁).1 (prev_pre h₂).1 hp
  sat := rspSatisfiable

/-- `vg_dsa_sign_random_prevalidated`. -/
theorem randomSignPre_verified :
    Verified RISCV64.target PrevalidatedSign.randomSign
      (Spec.Dsa.randomSignPrevalidatedContract RISCV64.abi RS.rsStack) :=
  show Verified RISCV64.target (RandomSign.codeWith preSigner.name preSigner.code) _ from
  Verified.of_correct (k := rspContract) (fun s (h : rspContract.pre s) => randomSignWith_correct preSigner s h.1 h.2)
    (fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => randomSignWith_ct preSigner s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂) rsp_implies

end VG.Proof.Dsa.RISCV64
