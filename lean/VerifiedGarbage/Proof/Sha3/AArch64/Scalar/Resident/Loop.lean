module
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBoundary
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident

import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Xor
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Advance
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLoop
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentMath
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Data.Finset.Attr
import VerifiedGarbage.Proof.Framework.Contract

/-!
# The scalar resident absorber: the invariant of its loop

The invariant of the loop over whole blocks (`Loop`): after `c` bytes of
data, the lanes represent the message followed by those bytes, and v19–v21
hold the data pointer, the length left and the rate. The registers it keeps
its values in are not the rounds' temporaries, the boundary's or the
callee-saved ones (`kept_not_temps`, `savedVec_not_kept`,
`preservedV_not_kept`), and the rates are those `select` tests
(`rates_select`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Resident
open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3.AArch64.Sha3.Vector.Resident (BulkPre rate st data len dataR bytesAt_add)
open VG.Spec.Sha3 (stateAt bytesAt)

/-- The loop's invariant, after `c` bytes of data: the lanes are `A`, which
the message followed by those bytes represents, and v19–v21 hold the data
pointer, the length left and the rate. -/
structure Loop (b : State) (c : Nat) (A : Spec.Sha3.State) (s : State) : Prop where
  c_le : c ≤ len b
  aligned : c % rate b = 0
  core : CoreState b A s
  mem : s.mem = b.mem
  dp : vdword (s.v .v19) 0 = data b + BitVec.ofNat 64 c
  left : vdword (s.v .v20) 0 = BitVec.ofNat 64 (len b - c)
  rt : vdword (s.v .v21) 0 = BitVec.ofNat 64 (rate b)
  repr : ∀ msg, stateAt b.mem (st b) = VG.Proof.Sha3.Rep (rate b) msg → msg.length % rate b = 0 →
    A = VG.Proof.Sha3.Rep (rate b) (msg ++ bytesAt b.mem (data b) c)

theorem kept_not_temps : ∀ q ∈ [VReg.v19, .v20, .v21, .v30, .v31],
    q ≠ .v24 ∧ q ≠ .v25 ∧ q ≠ .v28 ∧ q ≠ .v29 := by decide

theorem savedVec_not_kept : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v19 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v20 := by decide

theorem preservedV_not_kept : ∀ q ∈ preservedV, q ≠ .v19 ∧ q ≠ .v20 := by decide

theorem rates_select {r : Nat} (hr : r ∈ Spec.Sha3.rates) : r ∈ [72, 104, 136, 144] ++ [168] := by
  simp only [Spec.Sha3.rates, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  omega_using [hr]

end VG.Proof.Sha3.AArch64.Scalar.Resident
