module

public import VerifiedGarbage.Proof.Dsa.AArch64.Frame

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch

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
