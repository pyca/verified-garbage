module

import VerifiedGarbage.Proof.Dsa.Arm.Key.CT
import VerifiedGarbage.Proof.Dsa.Arm.Key.Correct
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Impl.Dsa.Arm.GenerateKey
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.TCB.Arm.Target

/-! # 32-bit ARM DSA key generation meets its contract -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.GenerateKey

/-- A 1024/160 call with an empty tape: the output at `0x1000`, `used` at
`0x7000`, the domain at `0x2000` and the working space at `0x8000`. -/
def generateKeySat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 424 | .r2 => 0x7000 | .r3 => 0x2000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0x14 else if a = 0x20001 then 1 else if a = 0x20004 then 0x80
    else if a = 0x20008 then 20 else if a = 0x2000d then 0x50 else if a = 0x20015 then 0x80
    else if a = 0x20019 then 0x24 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩, ⟨0x20000, 28⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩]

theorem generateKey_satisfiable : ∃ s, (Spec.Dsa.generateKeyContract Arm.abi 144).pre s := by
  sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
    [generateKeySat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using generateKeySat

theorem generateKey_verified (check derive : String) :
    Verified Arm.target (code check derive Generate.checkParameters Generate.deriveKey)
      (Spec.Dsa.generateKeyContract Arm.abi 144) :=
  ⟨generateKey_correct check derive, generateKey_constantTime check derive, generateKey_satisfiable⟩

/-- Key generation, calling the registered `vg_dsa_check_parameters` and `vg_dsa_derive_key`. -/
theorem generating_verified :
    Verified Arm.target (code "vg_dsa_check_parameters" Spec.Dsa.deriveKeyApi.name
      Generate.checkParameters Generate.deriveKey) (Spec.Dsa.generateKeyContract Arm.abi 144) :=
  generateKey_verified _ _

end VG.Proof.Dsa.Arm.Key
