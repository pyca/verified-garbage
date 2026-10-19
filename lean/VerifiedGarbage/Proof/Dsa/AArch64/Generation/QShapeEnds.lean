module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QShape
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64

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
