module
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.AArch64.Random

import VerifiedGarbage.Proof.Dsa.AArch64.RandomRange
import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Whole range-check correctness, including reads of the sampler's frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_inRange_ok {s : State} {B p q : Addr} {l : Nat} {as bs : List Byte}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hl : word s.mem B Random.oQLen = BitVec.ofNat 64 l)
    (hn : word s.mem B Random.oWidth = BitVec.ofNat 64 as.length)
    (hq : word s.mem B Random.oQ = q)
    (hp : p + BitVec.ofNat 64 as.length = off B (Random.oNonce + l))
    (hlen : as.length = bs.length) (hpos : 0 < as.length) (hbound : as.length < 2 ^ 64)
    (hra : ∀ i < as.length, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hrb : ∀ i < as.length, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 i) 1)
    (hva : ∀ i (h : i < as.length), s.mem (p + BitVec.ofNat 64 i) = as[i])
    (hvb : ∀ i (h : i < bs.length), s.mem (q + BitVec.ofNat 64 i) = bs[i]) :
    WP isa Random.inRange s fun t =>
      t.gpr .x8 = BitVec.ofNat 64 (if 0 < Spec.Dsa.decodeBE as ∧ Spec.Dsa.decodeBE as < Spec.Dsa.decodeBE bs then 1 else 0) ∧
      t.mem = s.mem ∧ Keep [.x0, .x4, .x2, .x8, .x10, .x12, .x9] s t := by
  unfold Random.inRange
  refine WP.seq (WP.mono (random_rangeInit_ok hs hsp hl hn hq)
    fun u ⟨hup, huq, hun, hu8, hu9, hum, hku⟩ => ?_)
  refine WP.seq (WP.mono (random_rangeLoop_ok (as := as) (bs := bs) hlen hpos hbound
    (hup.trans hp.symm) huq hun hu8 hu9
    (fun i hi => by rw [hku.rd, hku.wr]; exact hra i hi)
    (fun i hi => by rw [hku.rd, hku.wr]; exact hrb i hi)
    (fun i hi => by rw [hum]; exact hva i hi)
    (fun i hi => by rw [hum]; exact hvb i hi))
    fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_)
  have hb : v.gpr .x8 = BitVec.ofNat 64
      (if Spec.Dsa.decodeBE as < Spec.Dsa.decodeBE bs then 1 else 0) := by
    rw [← VG.Proof.Dsa.randomBorrow_eq as bs hlen, ← hv8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hz : (v.gpr .x10 == 0) = decide (Spec.Dsa.decodeBE as = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, hv9]
    exact VG.Proof.Dsa.randomOr_zero as
  refine WP.mono (random_rangeFinish_ok hb hz) fun t ⟨htz, htm, hkt⟩ =>
    ⟨htz, (htm.trans hvm).trans hum, ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
