module
public import VerifiedGarbage.Impl.Bignum.CrtLayout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
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
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
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
public import VerifiedGarbage.Proof.Dsa.AArch64.Parent
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constructing a child workspace header before loading its modulus -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev childBases : List Instr :=
  ([sth .x12 sW, sth .x1 Crt.sLink] : List Instr) ++ setBases

theorem childBases_ok {s : State} {B parent : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hsi : s.gpr .x1 = parent)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (hZ : 136 ≤ Z) :
    WP isa (.block childBases) s fun t =>
      Good t B Z w (word s.mem B (8 * sMinv)) ∧ word t.mem B (8 * Crt.sLink) = parent ∧
      Outside B 48 88 s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  unfold childBases
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem =
    (s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 w)).writeW (off B (8 * Crt.sLink)) parent) ?_ rfl rfl rfl)
    fun u ⟨hum, hku⟩ => ?_
  · brun [hdr_enc (show sW < 32 by decide), hdr_enc (show Crt.sLink < 32 by decide), hdi, hsi, h12, hs.st (d := 8 * sW) (Nat.le_trans (by decide) hZ), hs.st (d := 8 * Crt.sLink) hZ]
  have hudi := (hku.gpr .x0 (show Reg.x0 ∉ [] by decide)).trans hdi
  have hu12 := (hku.gpr .x12 (show Reg.x12 ∉ [] by decide)).trans h12
  refine WP.mono (setBases_ok (hs.congr hku.wr) hudi hu12 (Nat.le_trans (by decide) hZ))
    fun t ⟨htarr, hft, hkt⟩ => ?_
  have hks := hku.trans hkt
  refine ⟨⟨hs.congr hks.wr, (hks.gpr .x0 (by decide)).trans hdi, ⟨?_, ?_, htarr⟩⟩, ?_, ?_, hks.mono (by decide)⟩
  · rw [hft.word (Or.inl (by decide)) (by decide), hum,
      (writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hft.word (Or.inl (by decide)) (by decide), hum,
      (writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide)).word (Or.inl (by decide)) (by decide),
      (writeW_outside _ B _ (d := 8 * sW) (by decide)).word (Or.inr (by decide)) (by decide)]
  · rw [hft.word (Or.inr (by decide)) (by decide), hum, word_writeW_self]
  · intro x hx
    rw [hft x (by change ofs B x < 64 ∨ 128 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega), hum]
    rw [writeW_outside _ B _ (d := 8 * Crt.sLink) (by decide) x
      (by change ofs B x < 128 ∨ 136 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega)]
    exact writeW_outside _ B _ (d := 8 * sW) (by decide) x
      (by change ofs B x < 48 ∨ 56 ≤ ofs B x; change ofs B x < 48 ∨ 136 ≤ ofs B x at hx; omega)

end VG.Proof.Dsa.AArch64
