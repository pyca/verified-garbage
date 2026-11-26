module

public import VerifiedGarbage.Proof.Aes.SboxSpec
meta import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

-- separate module: the table is of the specification, evaluated once for every target.

/-!
# The AES S-box as a table, for the kernel

Evaluating `Spec.Aes.sbox` (or an ISA model's S-box, which is the same
computation) takes the kernel tens of milliseconds a byte. `sboxN` is its
table, packed in one number (`materialize_table`), from the specification's
computation on the truth tables of the 256 bytes (`SboxSpec.lean`), which
the kernel evaluates once, here: a check over the 256 bytes rewrites the
S-box to it (`sbox_eq_sboxN`), and reads each byte by a shift.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.Bitslice

/-- The truth tables of the bits of the S-box. -/
def sboxTabs : List Nat := sboxT ((List.range 8).map fun k => tableOf (fun c => c.testBit k) 256)

/-- The S-box on byte `c`, as a number. -/
def sboxN (c : Nat) : Nat := (row sboxTabs c).toNat

theorem sboxN_lt (c : Nat) : sboxN c < 256 := (row sboxTabs c).isLt

theorem sbox_eq_sboxN (b : Byte) : Spec.Aes.sbox b = BitVec.ofNat 8 (sboxN b.toNat) := by
  rw [sboxN, BitVec.ofNat_toNat, BitVec.setWidth_eq, sboxTabs, row_sboxT (by simp) b.isLt]
  refine congrArg _ (row_ext fun j hj => ?_).symm
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some, testBit_tableOf, b.isLt, decide_true, Bool.true_and]
  rfl

end VG.Proof.Aes

namespace VG

materialize_value Proof.Aes.sboxTabs
materialize_table Proof.Aes.sboxN 256

end VG
