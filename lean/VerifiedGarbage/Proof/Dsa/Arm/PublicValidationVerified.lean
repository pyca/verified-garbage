module

import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCT
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationABI
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.PublicValidationContract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Dsa.PublicValidationContract

/-! # The callable public-key validator satisfies its shared contract -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Impl.Dsa.Arm.PublicValidation

/-- A non-overlapping workspace and packed odd components, for contract satisfiability. -/
def satState (pLen qLen : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000
    | .r1 => 2048
    | .r2 => 0x10000
    | .r3 => BitVec.ofNat 32 (3 * pLen + qLen)
    | _ => 0
  sp := 0x30000
  n := false
  z := false
  c := false
  v := false
  mem a :=
    let d := (a - 0x1040).toNat
    if d < 16 then
      let ptr := 0x10000 + (match d / 4 with | 0 => 0 | 1 => pLen | 2 => pLen + qLen | _ => 2 * pLen + qLen)
      (BitVec.ofNat 32 ptr >>> (8 * (d % 4))).setWidth 8
    else 1
  rd := [⟨0x10000, 3 * pLen + qLen⟩]
  wr := [⟨0x1000, 16384⟩]

theorem implies {pLen qLen : Nat}
    (sat : (Proof.Dsa.PublicValidation.contract (layout pLen qLen) Arm.abi).pre (satState pLen qLen)) :
    (armContract pLen qLen).Implies (Proof.Dsa.PublicValidation.contract (layout pLen qLen) Arm.abi) where
  pre := by
    sig_implies_pre [Proof.Dsa.PublicValidation.pre, layout, Proof.Dsa.PublicValidation.contract, Proof.Dsa.PublicValidation.sig, armContract,
      ws, key, size, keyLen, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    all_goals exact (VG.Proof.X25519.Arm.addr_toNat _).symm
  post := by
    sig_implies_post [Proof.Dsa.PublicValidation.contract, Proof.Dsa.PublicValidation.sig, armContract,
      ws, key, size, keyLen, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  pub := by
    sig_implies_pub [Proof.Dsa.PublicValidation.contract, Proof.Dsa.PublicValidation.sig, armContract,
      ws, key, size, keyLen, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := ⟨satState pLen qLen, sat⟩

theorem verified (pLen qLen nP nQ : Nat)
    (wp : Width pLen nP := by constructor <;> decide) (wq : Width qLen nQ := by constructor <;> decide)
    (qp : qLen ≤ pLen := by decide) (q32 : qLen ≤ 32 := by decide)
    (sat : (Proof.Dsa.PublicValidation.contract (layout pLen qLen) Arm.abi).pre (satState pLen qLen) := by
      sig_pre [Proof.Dsa.PublicValidation.contract, Proof.Dsa.PublicValidation.sig, layout, satState,
        Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first | exact Region.disjoint_of_sep (by decide +kernel) | (unfold Proof.Dsa.PublicValidation.pre; decide +kernel) | decide +kernel) :
    Verified Arm.target (body pLen qLen) (Proof.Dsa.PublicValidation.contract (layout pLen qLen) Arm.abi) :=
  Verified.of_correct (correct wp wq qp q32) (ct wp wq qp q32) (implies sat)

end VG.Proof.Dsa.Arm.PublicValidation
