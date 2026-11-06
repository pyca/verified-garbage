module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorBackend
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Bulk
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Lit
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.UnrolledLit
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.ToAdditive
public import Aesop.BuiltinRules
public meta import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorBackend
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Bulk
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Resident
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Lit
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.UnrolledLit
meta import Mathlib.Tactic.NormNum.OfScientific
meta import Mathlib.Tactic.NormNum.DivMod
meta import Mathlib.Tactic.NormNum.Abs
meta import Mathlib.Data.Rat.Cast.Order
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.NormNum.Pow
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
meta import VerifiedGarbage.TCB.Axioms

/-!
# The scalar Keccak backend with its resident absorb

The scalar permutation (`VectorSlots`), whose sponge absorbs whole blocks
with the state in registers (`Scalar.Resident.bulk`) under the resident
absorber's guards (`Sha3.Vector.Resident.absorbWith`), falling back to the
ordinary streaming absorb for the rest.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.ResidentBackend

open VG VG.AArch64

def callee : Impl.Sha3.AArch64.Callee :=
  { VectorSlots.callee with
    absorbOverride := some (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorbWith
      Impl.Sha3.AArch64.Scalar.Resident.bulk VectorSlots.callee) }

/-! ## Summaries for the constant-time checks

`callee` differs from `VectorSlots.callee` only in its absorb, so the
summaries of the permutation, `pad` and `squeeze` are `VectorSlots.VSums`'s
(what `sponge_taint_summaries VSums callee saving` would prove again), and
only the absorb's are proven here, over them. -/

taint_summary VSums.absorb23 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x23, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb24 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb28 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb27 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

taint_summary VSums.absorb24_26 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm VectorSlots.VSums.rounds

/-- `sponge_taint_decide VSums`, with the summaries of the absorb above and
`VectorSlots.VSums`'s others, in the same order. -/
tactic_template "sha3_scalar_resident_taint_decide" : tactic => `(tactic|
  taint_decide_sum [
    VSums.absorb23, VSums.absorb24, VSums.absorb28, VSums.absorb27, VSums.absorb24_26,
    VectorSlots.VSums.pad28, VectorSlots.VSums.pad27, VectorSlots.VSums.pad26,
    VectorSlots.VSums.squeeze28, VectorSlots.VSums.squeeze27, VectorSlots.VSums.squeeze26,
    VectorSlots.VSums.perm28s, VectorSlots.VSums.perm27s, VectorSlots.VSums.perm26s,
    VectorSlots.VSums.permS, VectorSlots.VSums.perm28, VectorSlots.VSums.perm27,
    VectorSlots.VSums.perm26, VectorSlots.VSums.perm, VectorSlots.VSums.rounds, MlKemSums.ntt, MlKemSums.nttInv,
    MlKemSums.mul, MlKemSums.add, MlKemSums.sub, MlKemSums.cbd2, MlKemSums.encode12,
    MlKemSums.decode12, MlKemSums.ce, MlKemSums.dd, MlKemSums.ce1024, MlKemSums.dd1024])

theorem absorb_correct (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    ∃ t q, Exec isa (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorbWith
      Impl.Sha3.AArch64.Scalar.Resident.bulk VectorSlots.callee) a t q ∧
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q :=
  Sha3.Vector.Resident.absorb_correct VectorSlots.backend _ Resident.functional a hp

end VG.Proof.Sha3.AArch64.Scalar.ResidentBackend
