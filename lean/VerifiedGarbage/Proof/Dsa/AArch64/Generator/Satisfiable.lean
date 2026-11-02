module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.GeneratorStageContract

/-! # A state meets the generator stage's precondition

p = 2^(8 * pLen) − 1 (all ones), q = 1 and the exponent p − 1 at their
offsets of a working space of the generation's size, and an empty h tape. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Impl.Dsa.Generation.Layout

def satBase : Addr := 0x100000

/-- The byte at offset `o` of the working space. -/
def satByte (pLen o : Nat) : Byte :=
  if p ≤ o ∧ o < p + pLen then 0xFF
  else if exponent ≤ o ∧ o < exponent + pLen then (if o + 1 = exponent + pLen then 0xFE else 0xFF)
  else if o + 1 = q + Impl.Dsa.AArch64.Generator.qLen pLen then 1 else 0

def satMemory (pLen : Nat) : Mem := fun a => satByte pLen (a - satBase).toNat

def satState (pLen : Nat) : State where
  gpr r := match r with
    | .x0 => satBase | .x1 => BitVec.ofNat 64 (usedBytes pLen / 8) | .x2 => 0x200000 | .x3 => 0
    | _ => 0
  sp := 0x400000
  mem := satMemory pLen
  rd := [⟨0x200000, 0⟩]
  wr := [⟨satBase, usedBytes pLen / 8 * 8⟩]

theorem sat_p {pLen : Nat} (hb : Supported pLen) : pOf pLen (satMemory pLen) satBase = 2 ^ (8 * pLen) - 1 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_odd {pLen : Nat} (hb : Supported pLen) : pOf pLen (satMemory pLen) satBase % 2 = 1 := by
  rw [sat_p hb]
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_bits {pLen : Nat} (hb : Supported pLen) :
    Spec.Dsa.bitLength (pOf pLen (satMemory pLen) satBase) = 8 * pLen := by
  rw [sat_p hb]
  have low : 1 ≤ 8 * pLen := by rcases hb with rfl | rfl | rfl <;> decide
  have half : 2 ^ (8 * pLen) = 2 ^ (8 * pLen - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have pos := Nat.two_pow_pos (8 * pLen - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mpr ⟨by omega, by omega⟩

theorem sat_q {pLen : Nat} (hb : Supported pLen) : qOf pLen (satMemory pLen) satBase = 1 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_exponent {pLen : Nat} (hb : Supported pLen) :
    Spec.Rsa.bytesAt (satMemory pLen) (satBase + BitVec.ofNat 64 exponent) pLen =
      Spec.Dsa.encodeBE pLen ((pOf pLen (satMemory pLen) satBase - 1) / qOf pLen (satMemory pLen) satBase) := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem satisfiable {pLen : Nat} (hb : Supported pLen) : ∃ s, (contract pLen).pre s := by
  refine ⟨satState pLen, ?_⟩
  sig_pre [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact sat_odd hb
    | exact sat_bits hb
    | exact sat_exponent hb
    | (rw [sat_q hb]; decide)
    | (rcases hb with rfl | rfl | rfl <;> decide +kernel)
    | (rcases hb with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide +kernel))

end VG.Proof.Dsa.AArch64.Generator
