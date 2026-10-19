module

public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame

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
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
public import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Proof.Bignum.AArch64.Double
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
public import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
public import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
public import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
public import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
public import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Proof.Bignum.AArch64.Setup
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Dsa.AArch64.Load
public import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
public import VerifiedGarbage.Proof.Dsa.AArch64.Setup
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Initial source and count for DSA modular reduction -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- A temporary header slot lies entirely in the mutable child region. -/
theorem header_work {B : Addr} {w i : Nat} {mem mem' : Mem}
    (hi : 17 ≤ i) (hi' : i < 32) (h : Outside B (8 * i) 8 mem mem') :
    Frm B (workRanges w) mem mem' := by
  intro x hx
  apply h x
  have hb := hx (136, slot w 8 + tabBytes w - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  omega

/-- Initialize source and count without touching the prepared arrays. -/
theorem reduceInit_ok {s : State} {B p : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    {bytes : List Byte} {sp sl : Nat}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (_h64 : bytes.length < 2 ^ 64) :
    WP isa (.block (Arithmetic.reduceInit sp sl)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      (∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx) ∧
      word t.mem (off B o) (8 * Crt.sSrc) = p ∧
      word t.mem (off B o) (8 * Crt.sRem) = BitVec.ofNat 64 bytes.length ∧
      t.gpr .x3 = BitVec.ofNat 64 bytes.length ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hlo := hc.lo
  have hhi := hc.hi
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have hcl := hdr_lt_slot wx 8 (show Crt.sLink < 32 by decide)
  have hcs := hdr_lt_slot wx 8 (show Crt.sSrc < 32 by decide)
  have hcr := hdr_lt_slot wx 8 (show Crt.sRem < 32 by decide)
  refine WP.mono (WP.keep [.x5, .x1, .x3] (Q := fun t =>
    t.mem = (s.mem.writeW (off (off B o) (8 * Crt.sSrc)) p).writeW
      (off (off B o) (8 * Crt.sRem)) (BitVec.ofNat 64 bytes.length) ∧
    t.gpr .x3 = BitVec.ofNat 64 bytes.length) ?_ rfl rfl rfl) fun t ⟨⟨hmem, hz⟩, hk⟩ => ?_
  · unfold Arithmetic.reduceInit
    drun [Crt.ldw, hc.x0, hdr_enc hsp, hdr_enc hsl, hdr_enc (show Crt.sLink < 32 by decide),
      hdr_enc (show Crt.sSrc < 32 by decide), hdr_enc (show Crt.sRem < 32 by decide), hc.link, hp, hl,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot wx 8 by omega),
      hc.scr.ld (show 8 * sp + 8 ≤ Z by omega),
      hc.scr.ld (show 8 * sl + 8 ≤ Z by omega),
      hc.good.scr.st (show 8 * Crt.sSrc + 8 ≤ slot wx 8 by omega),
      hc.good.scr.st (show 8 * Crt.sRem + 8 ≤ slot wx 8 by omega)]
  have hs : Outside (off B o) (8 * Crt.sSrc) 8 s.mem
      (s.mem.writeW (off (off B o) (8 * Crt.sSrc)) p) := writeW_outside _ _ _ (by decide)
  have hr : Outside (off B o) (8 * Crt.sRem) 8
      (s.mem.writeW (off (off B o) (8 * Crt.sSrc)) p) t.mem := by
    rw [hmem]; exact writeW_outside _ _ _ (by decide)
  have hf := (header_work (by decide) (by decide) hs).trans (header_work (w := wx) (by decide) (by decide) hr)
  have ht := hc.of_frmT hf (workRanges_ok wx) hk.wr (hk.gpr .x0 (by decide))
  have hn := hc.good.scr.nowrap
  have harr : ∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx := by
    intro j hj
    rw [hmem, hdrStore_wv _ _ _ (by decide) hj hn, hdrStore_wv _ _ _ (by decide) hj hn]
  refine ⟨ht, ⟨ht.good, (harr aN (by decide)).trans hm.modulus, ?_⟩, harr, ?_, ?_, hz,
    hf, hk.mono (by decide)⟩
  · rw [hmem, hdrStore_word _ _ _ (by decide) (by decide) hn,
      hdrStore_word _ _ _ (by decide) (by decide) hn]
    exact hm.inverse
  · rw [hmem, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hmem, word_writeW_self]

end VG.Proof.Dsa.AArch64
