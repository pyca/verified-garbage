module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanBlocks
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.TCB.Arm.Isa

/-! Spread the highest public bound bit into the exact first-byte scalar mask. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

def smear32 (b : Byte) : BitVec 32 :=
  let a := b.setWidth 32 ||| b.setWidth 32 >>> 1
  let c := a ||| a >>> 2
  c ||| c >>> 4

theorem smear32_value (b : Byte) : (smear32 b).toNat = VG.Proof.Ffdh.KeyScalar.smearN b.toNat := by
  simp only [smear32, VG.Proof.Ffdh.KeyScalar.smearN, BitVec.toNat_or,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 32 by have := b.isLt; omega)]

theorem smear32_eq (b : Byte) : smear32 b = BitVec.ofNat 32 (VG.Proof.Ffdh.KeyScalar.smearN b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [smear32_value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have bound := VG.Proof.Ffdh.KeyScalar.smearN_lt b.toNat b.isLt
  omega

theorem smear_ok (s : State) {b : Byte} (byte : s.gpr .r3 = b.setWidth 32) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.smear) s fun t =>
      (t.gpr .r3 = smear32 b ∧ t.mem = s.mem) ∧ VG.Proof.X25519.Arm.Rest [.r3, .r12] s t := by
  refine withRest [.r3, .r12] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.smear : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.smear
  ffrun [byte, smear32]

end VG.Proof.Ffdh.Arm
