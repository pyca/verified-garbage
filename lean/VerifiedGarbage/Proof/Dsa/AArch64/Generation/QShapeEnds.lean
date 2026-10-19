module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QShape
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy

/-! Correctness of the two subgroup-candidate endpoint writes. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Ffdh.ParameterCandidate

theorem qShapeEnds_ok {s : State} {op : Addr} {n : Nat}
    (hn : 2 ≤ n) (hbound : n < 2 ^ 64)
    (hop : s.gpr .x13 = op) (hlen : s.gpr .x14 = BitVec.ofNat 64 n)
    (hr0 : InRegions (s.rd ++ s.wr) op 1)
    (hrn : InRegions (s.rd ++ s.wr) (off op (n - 1)) 1)
    (hw0 : InRegions s.wr op 1) (hwn : InRegions s.wr (off op (n - 1)) 1) :
    WP isa (.block Impl.Dsa.AArch64.Generation.qShapeEnds) s fun t =>
      t.mem = (s.mem.writeW op (s.mem op ||| (128#8))).writeW
        (off op (n - 1)) (s.mem (off op (n - 1)) ||| (1#8)) ∧
      Keep [.x0, .x2, .x4] s t := by
  refine WP.keep [.x0, .x2, .x4] ?_ rfl rfl rfl
  have hp : op + BitVec.ofNat 64 n - (1#64) = off op (n - 1) := by
    simp only [off]
    apply BitVec.sub_eq_iff_eq_add.mpr
    rw [BitVec.add_assoc]
    change op + BitVec.ofNat 64 n = op + (BitVec.ofNat 64 (n - 1) + BitVec.ofNat 64 1)
    rw [BitVec.ofNat_add_ofNat]
    rw [show n - 1 + 1 = n by omega]
  have hne : off op (n - 1) ≠ op := by
    simpa [off] using Offset.add_ofNat_ne op (show n - 1 < 2 ^ 64 by omega)
      (show 0 < 2 ^ 64 by decide) (show n - 1 ≠ 0 by omega)
  simp only [off] at hp hne hrn hwn ⊢
  unfold Impl.Dsa.AArch64.Generation.qShapeEnds
  brun [State.read, State.write, hop, hlen, hr0, hrn, hw0, hwn, hp, read_one,
    BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq,
    WriteBytes.writeW8_apply, hne]
  change (s.mem.writeW op (s.mem op ||| (128#8))).writeW _
    ((s.mem.writeW op (s.mem op ||| (128#8))) _ ||| (1#8)) = _
  rw [WriteBytes.writeW8_apply, ite_eq_right hne]

end VG.Proof.Dsa.AArch64.Generation
