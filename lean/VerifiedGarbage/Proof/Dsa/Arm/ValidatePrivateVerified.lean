module

public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateCT

/-!
# DSA private-key validation on 32-bit ARM: `Verified`

Correctness (`ValidatePrivate.lean`), constant time
(`ValidatePrivateCT.lean`), and a state satisfying the shared contract of
`Spec/Dsa/PrevalidatedSign.lean`, which `validatePrivArm` restates. The
function uses no stack beyond its arguments.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm

/-- A state satisfying the precondition of `vg_dsa_validate_private_key`:
1024/160 widths, the key at `0x2000` and the working space at `0x8000`. -/
def validatePrivSat : State where
  gpr r := match r with | .r0 => 0x2000 | .r1 => 424 | .r2 => 128 | .r3 => 20 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20001 then 0x80 else if a = 0x20005 then 0x08 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x20000, 8⟩]
  wr := [⟨0x8000, 16384⟩]

theorem validating_private_verified :
    Verified Arm.target PrevalidatedSign.validate (Spec.Dsa.validatePrivateKeyContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => validatePriv_correct hs) validatePriv_constantTime (by
    sig_implies [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, validatePrivArm,
      validatePrivPre, validatePrivRes, validatePrivLeak, validatePrivKey, arg, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [validatePrivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using validatePrivSat)

end VG.Proof.Dsa.Arm
