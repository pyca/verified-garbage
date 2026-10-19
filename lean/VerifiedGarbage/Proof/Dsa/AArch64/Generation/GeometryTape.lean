module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Geometry
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
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
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Spec.RsaOaep

/-! # Immutable entropy tapes are disjoint from every mutable generation area -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure GenerationTape (p : GenerationGeometry) where
  ptr : Addr
  bytes : List Byte
  bound : ptr.toNat + bytes.length ≤ 2 ^ 64
  size : bytes.length < 2 ^ 64
  arena : (⟨ptr, bytes.length⟩ : Region).Disjoint ⟨p.B, usedBytes p.pLen⟩
  frame : (⟨ptr, bytes.length⟩ : Region).Disjoint ⟨p.F, frameBytes⟩
  stack : (⟨ptr, bytes.length⟩ : Region).Disjoint (below p.F 16)

theorem GenerationTape.part {p : GenerationGeometry} (tape : GenerationTape p) {d n : Nat}
    (h : d + n ≤ usedBytes p.pLen) : (⟨tape.ptr, tape.bytes.length⟩ : Region).Disjoint (p.part d n) :=
  tape.arena.sub_right (p.part_sub h)

def GenerationTape.slice {p : GenerationGeometry} (tape : GenerationTape p) (used len : Nat)
    (room : used + len ≤ tape.bytes.length) : GenerationTape p where
  ptr := VG.Proof.Bignum.off tape.ptr used
  bytes := (tape.bytes.drop used).take len
  bound := by
    have hb := tape.bound
    have hl : ((tape.bytes.drop used).take len).length = len := by
      simp only [List.length_take, List.length_drop]; omega
    rw [hl]
    simp only [VG.Proof.Bignum.off, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [hb, room, tape.size]
  size := by simp only [List.length_take, List.length_drop]; omega_using [room, tape.size]
  arena := tape.arena.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))
  frame := tape.frame.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))
  stack := tape.stack.sub_left (Offset.sub_base _ (by
    simp only [List.length_take, List.length_drop]; omega))

theorem GenerationTape.source {p : GenerationGeometry} (tape : GenerationTape p) {s : State}
    {d n : Nat} (hd : d + n ≤ usedBytes p.pLen)
    (hr : ∀ i < tape.bytes.length, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off tape.ptr i) 1)
    (hv : ∀ i (hi : i < tape.bytes.length), s.mem (VG.Proof.Bignum.off tape.ptr i) = tape.bytes[i]'hi) :
    Src s (VG.Proof.Bignum.off p.B d) n tape.ptr tape.bytes :=
  ⟨hr, hv, fun i hi => out_scr (tape.part hd)
    (Offset.contains_base _ (by omega) (by omega_using [hi, tape.size]))⟩

end VG.Proof.Dsa.AArch64.Generation
