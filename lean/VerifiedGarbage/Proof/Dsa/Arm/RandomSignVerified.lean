module

import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect
public import VerifiedGarbage.Proof.Dsa.Arm.RandomCall
public import VerifiedGarbage.Impl.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
public import VerifiedGarbage.Proof.Dsa.Arm.SignCT
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedSignCT
import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified

/-! # The 32-bit ARM randomized signers meet their contracts

`vg_dsa_sign_random`, which calls the fully checked signer, and
`vg_dsa_sign_random_prevalidated`, which calls the signer for a validated
private key. -/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.RandomSign

/-- A 1024/160 call with an empty tape: the output at `0x1000`, `used` at
`0x7000`, the key at `0x2000` and the working space at `0x8000`. -/
def randomSignSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 40 | .r2 => 0x7000 | .r3 => 0x2000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0xa8 else if a = 0x20001 then 1 else if a = 0x20004 then 0x80
    else if a = 0x20008 then 20 else if a = 0x2000d then 0x50 else if a = 0x20015 then 0x60
    else if a = 0x2001d then 0x80 else if a = 0x20020 then 0x40 else if a = 0x20021 then 0x08 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x20000, 36⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

theorem randomSign_satisfiable : ∃ s, (Spec.Dsa.randomSignContract Arm.abi 144).pre s := by
  sig_implies_sat [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
    [randomSignSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using randomSignSat

/-- The fully checked signer, which accepts every key. -/
def checkedSigner : Signer where
  code := Entry.operation true
  valid := fun _ _ _ => true
  correct := fun _ hs => let ⟨t, s', e, ha, hp⟩ := sign_correct hs.1; ⟨t, s', e, ha, hp⟩
  constantTime := fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => sign_constantTime _ _ _ _ _ _ h₁.1 h₂.1 hp e₁ e₂
  stack := sign_armStack

/-- The signer for a validated private key. -/
def prevalidatedSigner : Signer where
  code := PrevalidatedSign.sign
  valid := Spec.Dsa.validatePrivateKeyBytes
  correct := fun _ hs => let ⟨t, s', e, ha, hp⟩ := prevSign_correct hs; ⟨t, s', e, ha, hp⟩
  constantTime := prevSign_constantTime
  stack := by decide +kernel

theorem randomSign_verified (name : String) :
    Verified Arm.target (code name (Entry.operation true)) (Spec.Dsa.randomSignContract Arm.abi 144) :=
  ⟨fun s h => randomSign_correct checkedSigner name s h rfl,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => randomSign_constantTime checkedSigner name s₁ s₂ t₁ t₂ u₁ u₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩,
    randomSign_satisfiable⟩

/-- The randomized signer, calling the registered `vg_dsa_sign`. -/
theorem randomSigning_verified : Verified Arm.target (code "vg_dsa_sign" (Entry.operation true))
    (Spec.Dsa.randomSignContract Arm.abi 144) :=
  randomSign_verified _

theorem randomPrevalidated_pre {s : State} (h : (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144).pre s) :
    (Spec.Dsa.randomSignContract Arm.abi 144).pre s ∧ RValid prevalidatedSigner s := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
  sig_and_intros <;> with_reducible assumption

/-- `randomSignSat` with `validPrivateKeyWitness` at `0x2000`. -/
def randomPrevSat : State where
  gpr := randomSignSat.gpr
  sp := randomSignSat.sp
  n := false
  z := false
  c := false
  v := false
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else randomSignSat.mem a
  rd := randomSignSat.rd
  wr := randomSignSat.wr

theorem randomPrevSat_key :
    Spec.Rsa.bytesAt randomPrevSat.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness :=
  bytesAt_window (base := 0x2000) VG.Proof.Dsa.validPrivateKeyWitness_length (by decide) fun _ h₁ h₂ =>
    ite_eq_left ⟨h₁, h₂⟩

theorem randomPrev_satisfiable : ∃ s, (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144).pre s := by
  refine ⟨randomPrevSat, ?_⟩
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
  sig_and_intros
  all_goals first
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)
    | (change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt randomPrevSat.mem 0x2000 424) = true
       rw [randomPrevSat_key]
       exact VG.Proof.Dsa.validPrivateKeyWitness_valid)

theorem randomSignPrevalidated_verified (name : String) :
    Verified Arm.target (code name PrevalidatedSign.sign)
      (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144) :=
  ⟨fun s h => randomSign_correct prevalidatedSigner name s (randomPrevalidated_pre h).1 (randomPrevalidated_pre h).2,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => randomSign_constantTime prevalidatedSigner name s₁ s₂ t₁ t₂ u₁ u₂
      (randomPrevalidated_pre h₁) (randomPrevalidated_pre h₂),
    randomPrev_satisfiable⟩

/-- The randomized signer for a validated key, calling the registered
`vg_dsa_sign_prevalidated`. -/
theorem randomSigningPrevalidated_verified :
    Verified Arm.target (code "vg_dsa_sign_prevalidated" PrevalidatedSign.sign)
      (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144) :=
  randomSignPrevalidated_verified _

end VG.Proof.Dsa.Arm
