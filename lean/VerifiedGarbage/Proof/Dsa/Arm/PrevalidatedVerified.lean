module

public import VerifiedGarbage.Proof.Dsa.Arm.Prevalidated
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Proof.Dsa.Arm.Verified
import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedCT

/-!
# DSA public-key validation and prevalidated verification on 32-bit ARM: `Verified`

Untrusted: everything here is checked by Lean. Correctness
(`Prevalidated.lean`), constant time (`PrevalidatedCT.lean`), and states
satisfying the shared contracts of `Spec/Dsa/Prevalidated.lean`, which
`validateArm` and `prevArm` restate. Neither function uses the stack beyond
its arguments.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm

/-- A state satisfying the precondition of `vg_dsa_validate_public_key`:
1024/160 widths, the key at `0x2000` and the working space at `0x8000`. -/
def validateSat : State where
  gpr r := match r with | .r0 => 0x2000 | .r1 => 404 | .r2 => 128 | .r3 => 20 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20001 then 0x80 else if a = 0x20005 then 0x08 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x20000, 8⟩]
  wr := [⟨0x8000, 16384⟩]

theorem validate_verified :
    Verified Arm.target Prevalidated.validate (Spec.Dsa.validatePublicKeyContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => validate_correct hs) validate_constantTime (by
    sig_implies [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, validateArm, validatePre,
      validateRes, validateLeak, validateKey, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [validateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using validateSat)

/-- `verifySat` with `VG.Proof.Dsa.validKeyWitness` at `0x2000`. -/
def prevSat : State where
  gpr := verifySat.gpr
  sp := verifySat.sp
  n := false
  z := false
  c := false
  v := false
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2194 then
    VG.Proof.Dsa.validKeyWitness[a.toNat - 0x2000]?.getD 0 else verifySat.mem a
  rd := verifySat.rd
  wr := verifySat.wr

/-- The octets of a memory that holds `l` from `base` on. -/
theorem bytesAt_window {m : Mem} {base n : Nat} {l : List Byte} (hl : l.length = n) (hb : base + n < 2 ^ 64)
    (hm : ∀ a : Addr, base ≤ a.toNat → a.toNat < base + n → m a = l[a.toNat - base]?.getD 0) :
    Spec.Rsa.bytesAt m (BitVec.ofNat 64 base) n = l := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hl]
  · intro i h₁ h₂
    have hi : i < n := by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁; exact h₁
    have e : (BitVec.ofNat 64 base + BitVec.ofNat 64 i).toNat = base + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [hm _ (by omega) (by omega), e, Nat.add_sub_cancel_left, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem prevSat_key :
    Spec.Rsa.bytesAt prevSat.mem (State.addr (prevSat.gpr .r0)) (prevSat.gpr .r1).toNat =
      VG.Proof.Dsa.validKeyWitness :=
  bytesAt_window (base := 0x2000) VG.Proof.Dsa.validKeyWitness_length (by decide) fun _ h₁ h₂ =>
    ite_eq_left ⟨h₁, h₂⟩

/-- The shared verifier's precondition and a key that validates give the
prevalidated verifier's. -/
theorem prevalidatedPre_of {s : State} (h : (Spec.Dsa.verifyContract Arm.abi 0).pre s)
    (hv : Spec.Dsa.validatePublicKeyBytes (s.gpr .r2).toNat (s.gpr .r3).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) = true) :
    (Spec.Dsa.verifyPrevalidatedContract Arm.abi 0).pre s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
  simp only [Arm.State.addr] at hv
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem prevSat_ok : ∃ s, (Spec.Dsa.verifyPrevalidatedContract Arm.abi 0).pre s := by
  have ho : ∃ s, (Spec.Dsa.verifyContract Arm.abi 0).pre s ∧ s = prevSat := by
    sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [prevSat, verifySat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using prevSat
  obtain ⟨s, h, rfl⟩ := ho
  refine ⟨_, prevalidatedPre_of h ?_⟩
  rw [prevSat_key]
  exact VG.Proof.Dsa.validKeyWitness_valid

/-- `prevalidated_correct`, in the form `Verified.of_correct` takes. -/
theorem prevalidated_correct' (s : State) (h : prevArm.pre s) :
    ∃ t s', Exec Arm.target.isa Prevalidated.verify s t s' ∧ Arm.target.abiPreserved s s' ∧ prevArm.post s s' :=
  prevalidated_correct h

theorem prevalidated_verified :
    Verified Arm.target Prevalidated.verify (Spec.Dsa.verifyPrevalidatedContract Arm.abi 0) :=
  Verified.of_correct prevalidated_correct' prevalidated_constantTime
    { pre := by
        sig_implies_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, prevArm, prevPre, verifyPre, arg,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      post := by
        sig_implies_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, prevArm, verifyArm, verifyRes,
          arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr,
          BitVec.add_zero]
      pub := by
        sig_implies_pub [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, prevArm, verifyArm, verifyLeak,
          verifyRes, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
          Arm.stackArgAddr, BitVec.add_zero]
      sat := prevSat_ok }

end VG.Proof.Dsa.Arm
