module

import VerifiedGarbage.Proof.Dsa.Arm.GenerateContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheckCT
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDerive
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDeriveCT
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# DSA domain checks and key derivation on 32-bit ARM: `Verified`

Untrusted: everything here is checked by Lean. Correctness
(`GenerateCheck.lean`, `GenerateDerive.lean`), constant time
(`GenerateCheckCT.lean`, `GenerateDeriveCT.lean`), and states satisfying the
shared contracts of `Spec/Dsa/Derive.lean`, which `checkArm` and `deriveArm`
restate. Neither function uses the stack beyond its arguments.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm

/-- A state satisfying the precondition of `vg_dsa_check_parameters`:
1024/160 widths, the domain at `0x2000` and the working space at `0x8000`. -/
def checkSat : State where
  gpr r := match r with | .r0 => 0x2000 | .r1 => 276 | .r2 => 128 | .r3 => 20 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20001 then 0x80 else if a = 0x20005 then 0x08 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x20000, 8⟩]
  wr := [⟨0x8000, 16384⟩]

/-- A state satisfying the precondition of `vg_dsa_derive_key`: as
`checkSat`, x at `0x4000` and the output at `0x1000`. -/
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

theorem check_verified :
    Verified Arm.target Generate.checkParameters (Proof.Dsa.checkParametersContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => check_correct hs) check_constantTime (by
    sig_implies [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, checkArm, checkPre, checkRes,
      checkParams, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr,
      BitVec.add_zero] [checkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using checkSat)

theorem derive_verified : Verified Arm.target Generate.deriveKey (Spec.Dsa.deriveKeyContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => derive_correct hs) derive_constantTime (by
    sig_implies [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, deriveArm, derivePre, deriveRes, deriveLeak,
      deriveParams, deriveX, arg, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
      Arm.stackArgAddr, BitVec.add_zero] [deriveSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using deriveSat)

end VG.Proof.Dsa.Arm
