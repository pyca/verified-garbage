module

public import VerifiedGarbage.Proof.Dsa.Arm.GenerateContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.DomainChecked
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheckCT
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDerive
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDeriveCT
import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# DSA domain checks and key derivation on 32-bit ARM: `Verified`

Untrusted: everything here is checked by Lean. Correctness
(`GenerateCheck.lean`, `GenerateDerive.lean`), constant time
(`GenerateCheckCT.lean`, `GenerateDeriveCT.lean`), and states satisfying the
shared contracts of `Spec/Dsa/Derive.lean`, which `checkArm` and `deriveArm`
restate, and of `Spec/Dsa/DomainChecked.lean`'s derivation, which
`deriveCheckedArm` restates. No function uses the stack beyond its arguments.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm

/-- A state satisfying the precondition of `vg_dsa_derive_key`: x at
`0x4000` and the output at `0x1000`. -/
def deriveSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 424 | .r2 => 0x2000 | .r3 => 276 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0x80 else if a = 0x20005 then 0x40 else if a = 0x20008 then 20
    else if a = 0x2000d then 0x80 else if a = 0x20011 then 0x08 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x4000, 20⟩, ⟨0x20000, 20⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x8000, 16384⟩]

theorem derive_verified : Verified Arm.target Generate.deriveKey (Spec.Dsa.deriveKeyContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => derive_correct hs) derive_constantTime (by
    sig_implies [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, deriveArm, derivePre, deriveRes, deriveLeak,
      deriveParams, deriveX, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
      Arm.stackArgAddr, BitVec.add_zero] [deriveSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using deriveSat)

/-- The domain of `VG.Proof.Dsa.validKeyWitness`, its first 276 bytes. -/
def validDomainWitness : List Byte := VG.Proof.Dsa.validKeyWitness.take 276

theorem validDomainWitness_length : validDomainWitness.length = 276 := by
  simp only [validDomainWitness, List.length_take, VG.Proof.Dsa.validKeyWitness_length]; rfl

theorem validDomainWitness_valid : Spec.Dsa.checkParametersBytes 128 20 validDomainWitness = true := by
  decide +kernel

/-- `deriveSat` with `validDomainWitness` at `0x2000`. -/
def deriveCheckedSat : State where
  gpr := deriveSat.gpr
  sp := deriveSat.sp
  n := false
  z := false
  c := false
  v := false
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2114 then
    validDomainWitness[a.toNat - 0x2000]?.getD 0 else deriveSat.mem a
  rd := deriveSat.rd
  wr := deriveSat.wr

theorem deriveCheckedSat_domain :
    Spec.Rsa.bytesAt deriveCheckedSat.mem (State.addr (deriveCheckedSat.gpr .r2)) (deriveCheckedSat.gpr .r3).toNat =
      validDomainWitness :=
  bytesAt_window (base := 0x2000) validDomainWitness_length (by decide) fun _ h₁ h₂ => ite_eq_left ⟨h₁, h₂⟩

/-- The shared derivation's precondition and a domain that passes its check
give the checked derivation's. -/
theorem deriveCheckedPre_of {s : State} (h : (Spec.Dsa.deriveKeyContract Arm.abi 0).pre s)
    (hv : Spec.Dsa.checkParametersBytes (stackArg s 0).toNat (stackArg s 2).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract Arm.abi 0).pre s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero] at h
  sig_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, arg, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
  simp only [Arm.State.addr] at hv
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem deriveCheckedSat_ok : ∃ s, (Spec.Dsa.deriveKeyDomainCheckedContract Arm.abi 0).pre s := by
  have ho : ∃ s, (Spec.Dsa.deriveKeyContract Arm.abi 0).pre s ∧ s = deriveCheckedSat := by
    sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [deriveCheckedSat, deriveSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using deriveCheckedSat
  obtain ⟨s, h, rfl⟩ := ho
  refine ⟨_, deriveCheckedPre_of h ?_⟩
  rw [deriveCheckedSat_domain]
  exact validDomainWitness_valid

theorem deriveChecked_implies : deriveCheckedArm.Implies (Spec.Dsa.deriveKeyDomainCheckedContract Arm.abi 0) :=
    { pre := by
        sig_implies_pre [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, deriveCheckedArm, deriveArm,
          derivePre, deriveParams, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
          Arm.stackArgAddr, BitVec.add_zero]
      post := by
        sig_implies_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, deriveCheckedArm, deriveArm,
          deriveRes, deriveParams, deriveX, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      pub := by
        sig_implies_pub [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, deriveCheckedArm, deriveArm,
          deriveLeak, deriveRes, deriveParams, deriveX, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      sat := deriveCheckedSat_ok }

theorem deriveChecked_verified :
    Verified Arm.target Generate.deriveChecked (Spec.Dsa.deriveKeyDomainCheckedContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => deriveChecked_correct hs) deriveChecked_constantTime deriveChecked_implies

end VG.Proof.Dsa.Arm
