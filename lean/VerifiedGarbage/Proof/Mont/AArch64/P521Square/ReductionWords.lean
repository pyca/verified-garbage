module
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
public import VerifiedGarbage.Impl.Mont.AArch64.P521Square
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Mont.AArch64.Blocks
public import VerifiedGarbage.Proof.Mont.AArch64.Csub
public import VerifiedGarbage.Proof.Mont.AArch64.Rounds


@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Proof.Ed25519.Word64

abbrev Word := BitVec 64

/-- Little-endian value of a word list. -/
def value : List Word → Nat
  | [] => 0
  | x :: xs => x.toNat + 2^64 * value xs

/-- An addition chain, retaining its last carry. -/
def addWords : List Word → List Word → Bool → List Word × Bool
  | x::xs, y::ys, c =>
    let r := addWords xs ys (carryOut x y c)
    (addCarry x y c :: r.1, r.2)
  | _, _, c => ([],c)

/-- The low input with all bits above bit 520 set. -/
def foldLow (w : Nat → Word) : List Word :=
  (List.range 8).map w ++ [w 8 ||| (BitVec.ofNat 64 (2^64-1) <<< 9)]

/-- The input shifted right by 521 bits. -/
def foldHigh (w : Nat → Word) : List Word :=
  (List.range 8).map (fun i => ((w (i+9) ++ w (i+8)).extractLsb' 9 64)) ++ [w 16 >>> 9]

def folded (w : Nat → Word) : List Word × Bool := addWords (foldLow w) (foldHigh w) true

/-- Subtract the complement of the incoming carry through nine words. -/
def corrected (xs : List Word) (c : Bool) : List Word :=
  let r := (addWords xs (List.replicate 9 (~~~(0 : Word))) c).1
  r.take 8 ++ [r.getD 8 0 &&& BitVec.ofNat 64 511]

/-- The nine output words of the cyclic shift right by 55 bits. -/
def rotated (w : Nat → Word) : List Word :=
  let top := w 8 ||| (w 0 <<< 9)
  (List.range 7).map (fun i => ((w (i+1) ++ w i).extractLsb' 55 64)) ++
    [((top ++ w 7).extractLsb' 55 64), top >>> 55]

end VG.Proof.Mont.AArch64.P521Square
