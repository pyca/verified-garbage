module

import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract
meta import VerifiedGarbage.Proof.Dsa.FixedBaseCombContract
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit
meta import VerifiedGarbage.TCB.Audit

/-! Algebraic checks of the comb contracts' representation and frame policy
(`Proof/Dsa/FixedBaseCombContract.lean`).
These are synthetic small-field identities, not cryptographic known-answer
vectors or a proof of an assembly implementation. -/

open VG.Spec
open VG.Proof.Dsa.FixedBaseComb
open VG.Impl.Dsa.FixedBaseComb (Layout)

private def layout : Layout :=
  { n := 1, e := 1, modulus := 0, base := 8, exponent := 16, result := 24,
    scratch := [(24, 40)], size := 400, context := 128 }

example : LayoutValid layout := by
  simp [LayoutValid, layout, contextWords, Rsa.FixedBaseComb.entries, Rsa.FixedBaseComb.teeth]
example : ¬ LayoutValid { layout with context := 32 } := by
  simp [LayoutValid, layout, contextWords, Rsa.FixedBaseComb.entries, Rsa.FixedBaseComb.teeth]
example : ¬ LayoutValid { layout with size := 399 } := by
  simp [LayoutValid, layout, contextWords, Rsa.FixedBaseComb.entries, Rsa.FixedBaseComb.teeth]
example : ¬ LayoutValid { layout with scratch := [(128, 8)] } := by
  simp [LayoutValid, layout, contextWords, Rsa.FixedBaseComb.entries, Rsa.FixedBaseComb.teeth]
example : ¬ LayoutValid { layout with n := 0 } := by
  simp [LayoutValid, layout, contextWords, Rsa.FixedBaseComb.entries, Rsa.FixedBaseComb.teeth]
example : ¬ LayoutValid { layout with e := 0 } := by
  simp [LayoutValid, layout, contextWords, Rsa.FixedBaseComb.entries, Rsa.FixedBaseComb.teeth]

/-- Independently replay Montgomery comb rows in a small prime field. Each
entry fits one word, even for deliberately padded storage. R is generally
not one, so this also checks the table's Montgomery scaling. -/
private def replay (L : Layout) (p : Nat) (values : List (BitVec 64)) (x : Nat) : Nat :=
  let rows := Rsa.FixedBaseComb.rows (32 * L.e)
  let r := 2 ^ (64 * L.n) % p
  let inverse := Rsa.powMod r (p - 2) p
  let result := (List.range rows).reverse.foldl (fun acc i =>
    let digit := (List.range 5).foldl (fun d j => d + (x / 2 ^ (i + j * rows) % 2) * 2 ^ j) 0
    let entry := (values[2 * L.n + digit * L.n]!).toNat
    acc * acc * entry * inverse * inverse % p) r
  result * inverse % p

private def checkContext (n e : Nat) : Bool :=
  let L := { layout with n := n, e := e }
  [3, 17, 19].all fun p => [0, 1, 2, p - 1, p + 1].all fun g =>
    let values := context L p g
    values.length == contextWords L &&
    values.take (2 * n) == Rsa.toWords p n ++ Rsa.toWords (2 ^ (128 * n) % p) n &&
    [0, 1, 31, 2 ^ (32 * e - 1), 2 ^ (32 * e) - 1].all fun x =>
      replay L p values x == Rsa.powMod g x p

-- Every DSA keygen storage shape, including 224/256-bit zero-padded comb rows.
#guard [(16, 5), (32, 5), (32, 7), (32, 8), (48, 8)].all fun (n, e) => checkContext n e

#assert_spec_origin
