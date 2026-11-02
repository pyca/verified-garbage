module

public import VerifiedGarbage.Impl.Dsa.Arm.Pow
public import VerifiedGarbage.Impl.Dsa.Arm.Stream
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # DSA's reductions and products as functions on 32-bit ARM

`vg_dsa_reduce_{n}` and `vg_dsa_mulmod_{n}` (`Proof/Dsa/ModArithContract.lean`) reduce
the `r3` bytes at `r2` (`reduceStream`) or multiply slots 8 and 11
(`ordinaryMul`), into slot 9, with the register saves of `Pow.lean`.
Multiplication sets up the complete Montgomery context; byte reduction
needs only the modulus and inverse, so it avoids computing unused R².
The reduction keeps the bytes' address in `r11` and their length in the
header, at byte 44, across the lightweight setup.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Arith
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Impl.Dsa.Arm.Pow

/-- The header's word that keeps the bytes' length. -/
def lenAt : Nat := 44

def reduceBody (n : Nat) : Prog isa :=
  .seq (.block (save ++ [.mov .r11 (.reg .r2), .str .r3 .r12 lenAt])) <|
  .seq (Context.light n) <|
  .seq (.block [.ldr .lr .r12 lenAt, .dp .add .lr .lr (.reg .r11)]) <|
  .seq (reduceStream n) (.block restore)

def mulBody (n : Nat) : Prog isa :=
  .seq (.block save) (.seq (Context.call n) (.seq (ordinaryMul n) (.block restore)))

def reduceLayout (n : Nat) : Impl.Dsa.ModArith.ReduceLayout where
  n := n
  modulus := modS n
  result := resS n
  scratch := scratch n
  size := contextBytes n

def mulLayout (n : Nat) : Impl.Dsa.ModArith.MulLayout where
  n := n
  modulus := modS n
  a := baseS n
  b := expS n
  result := resS n
  scratch := scratch n
  size := contextBytes n

def reduceName (n : Nat) : String := s!"vg_dsa_reduce_{(reduceLayout n).n}"

def mulName (n : Nat) : String := s!"vg_dsa_mulmod_{(mulLayout n).n}"

/-- The arguments of a call: the working space `r12` and its length, kept in
`r11` across the call. -/
def head (n : Nat) : List Instr :=
  [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 (BitVec.ofNat 16 (contextBytes n / 8))]

/-- A reduction of the `lr - r11` bytes at `r11`. -/
def reduceCall (n : Nat) : Prog isa :=
  .seq (.block ([.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11)] ++ head n))
    (.seq (.call (reduceName n) (reduceBody n)) (.block [.mov .r12 (.reg .r11)]))

def mulCall (n : Nat) : Prog isa :=
  .seq (.block (head n)) (.seq (.call (mulName n) (mulBody n)) (.block [.mov .r12 (.reg .r11)]))

end VG.Impl.Dsa.Arm.Arith
