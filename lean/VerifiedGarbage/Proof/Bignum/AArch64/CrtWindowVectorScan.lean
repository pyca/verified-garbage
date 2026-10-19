module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorInner
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
import Mathlib.Data.Int.ModEq
meta import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorRow
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
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! The 32-entry scan consumes every row and leaves the selected 64-byte block. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

structure ScanInv (s : State) (base : Addr) (stride v j : Nat) (t : State) : Prop where
  mem : t.mem = s.mem
  keep : Keep [.x14, .x16] s t
  ptr : t.gpr .x16 = base + BitVec.ofNat 64 (stride * j)
  index : t.v .v23 = dup2 (BitVec.ofNat 64 j)
  digit : t.v .v22 = dup2 (BitVec.ofNat 64 v)
  one : t.v .v24 = dup2 1
  value : ∀ i < 4, t.v (acc i) = if v < j then
    s.mem.read (base + BitVec.ofNat 64 (stride * v + 16 * i)) 16 else 0

theorem decVector_ok (s : State) :
    WP isa (.block [.subImm .x .x14 .x14 1]) s fun t =>
      (t.gpr .x14 = s.gpr .x14 - BitVec.ofNat 64 1 ∧ t.mem = s.mem ∧ t.v = s.v) ∧
      Keep [.x14] s t := by
  refine WP.keep [.x14] ?_ rfl rfl rfl
  brun
  exact RegUpd.v_write _ _ _ _

theorem scanStep_ok {s t : State} {base : Addr} {stride v j : Nat}
    (hj : j < 32) (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (hI : ScanInv s base stride v j t)
    (hld : ∀ j < 32, ∀ i < 4,
      InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (stride * j + 16 * i)) 16) :
    WP isa (.block (inner ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      ScanInv s base stride v (j + 1) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff]
  refine WP.mono (inner_ok hj hv hI.index hI.digit hI.one (fun i hi => by
    rw [hI.keep.rd, hI.keep.wr, hI.ptr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hld j hj i hi)) fun a ⟨⟨ha, hp, hm, h23, h22, h24⟩, ka⟩ => ?_
  refine WP.mono (decVector_ok a) fun u ⟨⟨hu, hum, huv⟩, ku⟩ => ?_
  refine ⟨⟨hum.trans (hm.trans hI.mem), ((hI.keep.trans ka).trans ku).mono (by decide),
    ?_, ?_, ?_, ?_, ?_⟩, hu.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x14 (by decide)))⟩
  · rw [ku.gpr .x16 (by decide), hp, hI.ptr, hI.keep.gpr .x6 (by decide), hs,
      BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.mul_one]
  · rw [huv, h23]
  · rw [huv, h22, hI.digit]
  · rw [huv, h24, hI.one]
  · intro i hi
    rw [huv, ha i hi, hI.mem, hI.ptr, BitVec.add_assoc, ← BitVec.ofNat_add, hI.value i hi]
    by_cases he : j = v
    · subst j
      simp only [ite_true, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
    · have heq : v < j + 1 ↔ v < j := by omega
      simp only [he, ite_false, heq]

/-- Exact 32-row scan. Its final value does not depend on the prior contents
of the accumulator registers, which the caller clears before entering. -/
theorem scan_ok {s : State} {base : Addr} {stride v : Nat}
    (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (hc : s.gpr .x14 = BitVec.ofNat 64 32) (h0 : ScanInv s base stride v 0 s)
    (hld : ∀ j < 32, ∀ i < 4,
      InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (stride * j + 16 * i)) 16) :
    WP isa (countLoop .x14 inner) s (ScanInv s base stride v 32) := by
  unfold countLoop
  exact wp_countdown (by decide) (by decide) (fun j => ScanInv s base stride v j)
    (fun j hj t hI _ => scanStep_ok hj hv hs hI hld) h0 hc

theorem scan_ct :
    RelCT isa (Two fun (p : Addr × BitVec 64 × BitVec 64) s =>
      s.gpr .x16 = p.1 ∧ s.gpr .x6 = p.2.1 ∧ s.gpr .x14 = p.2.2)
      (countLoop .x14 inner) (fun _ _ => True) := by
  apply two_taint [.x16, .x6, .x14]
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm
  · taint_decide

end VG.Proof.Bignum.AArch64.WindowVector
