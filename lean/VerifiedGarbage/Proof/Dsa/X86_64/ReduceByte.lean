module
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame

import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # A complete byte step of DSA's streaming modular reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Facts retained as the byte loop advances. -/
structure ReduceState (s : State) (B : Addr) (Z o w wx m : Nat) (minv : BitVec 64)
    (p : Addr) (bytes : List Byte) (acc : Nat) : Prop where
  ctx : SubCtx s B Z o w wx minv
  modulus : ModCtx s (off B o) (slot wx 8) wx minv m
  multiplier : wv s.mem (off B o) (slot wx aR2) wx = 256 * 2 ^ (64 * wx) % m
  high : ∀ i < wx, i ≠ 0 → word s.mem (off B o) (slot wx aX + 8 * i) = 0
  value : wv s.mem (off B o) (slot wx aY) wx = acc
  reduced : acc < m
  pointer : word s.mem (off B o) (8 * Crt.sSrc) = p
  remaining : word s.mem (off B o) (8 * Crt.sRem) = BitVec.ofNat 64 bytes.length
  source : Src s B Z p bytes

/-- One step consumes one readable byte, performs Horner reduction, and
branches only on whether the public remaining length is zero. -/
theorem reduceByte_ok (M : Mont) {s : State} {B p : Addr} {Z o w wx m acc : Nat}
    {minv : BitVec 64} {b : Byte} {bs : List Byte}
    (h : ReduceState s B Z o w wx m minv p (b :: bs) acc)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (hm : 255 < m) (hodd : m % 2 = 1)
    (hlen : (b :: bs).length < 2 ^ 64) :
    WP isa (Arithmetic.reduceByte M.mm) s fun t =>
      ReduceState t B Z o w wx m minv (p + 1) bs ((256 * acc + b.toNat) % m) ∧
      t.zf = some (decide (bs.length = 0)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hr : InRegions (s.rd ++ s.wr) p 1 := by simpa using h.source.rd 0 (by simp)
  have hb : s.mem p = b := by
    have hv := h.source.val 0 (by simp)
    change s.mem (p + 0) = b at hv
    exact (congrArg s.mem (BitVec.add_zero p)).symm.trans hv
  have hz := h.ctx.good.scr.nowrap
  have hslot := slot_le (w := wx) (show aX < 8 by decide)
  unfold Arithmetic.reduceByte seqs
  refine WP.seq (WP.mono (reduceRead_context h.ctx h.modulus (by omega) h.pointer hr h.high)
    fun u ⟨hcu, hmu, hbyte, hkept, hhigh, hptr, hrem, hfu, hku⟩ => ?_)
  rw [hb] at hbyte
  have huy := (hkept aY (by decide) (by decide)).trans h.value
  have hur := (hkept aR2 (by decide) (by decide)).trans h.multiplier
  refine WP.seq (WP.mono (reduceStep_ok M hcu.good (Nat.le_refl _) hw hw'
    hmu.modulus hodd hmu.inverse huy h.reduced hbyte (by have := b.isLt; omega) hur)
    fun v ⟨hgv, hv, hfv, hkv⟩ => ?_)
  have hcv := arrays_context hcu hfv (by decide) hkv
  have hn := (hfv.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hmu.modulus
  have hi : ((word v.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfv.word0_of_not_mem (by decide) (by decide) hz (by omega)]
    exact hmu.inverse
  have hmv : ModCtx v (off B o) (slot wx 8) wx minv m := ⟨hgv, hn, hi⟩
  have hvr := (hfv.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans hur
  have hvptr := (hfv.hslot (i := Crt.sSrc) (by decide)).trans hptr
  have hvrem := ((hfv.hslot (i := Crt.sRem) (by decide)).trans hrem).trans h.remaining
  have hvhigh : ∀ i < wx, i ≠ 0 → word v.mem (off B o) (slot wx aX + 8 * i) = 0 := by
    intro i hi hne
    rw [hfv.word_eq (fun j hj => by
      have hne : aX ≠ j := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> decide
      have := slot_sep (w := wx) hne
      omega) (by omega)]
    exact hhigh i hi hne
  have hfw := hfu.trans (arrays_work hfv (by decide))
  have hkw := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.mono (reduceCount_ok hcv hmv hvrem (by simp) hlen)
    fun t ⟨hct, hmt, htrem, htz, hft, hftw, hkt⟩ => ?_
  have hf := hfw.trans hftw
  have hk := (hkw.trans hkt).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have htarr : ∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv v.mem (off B o) (slot wx j) wx := by
    intro j hj
    exact hft.wv (Or.inr (by have := hdr_lt_slot wx j (show Crt.sRem < 32 by decide); omega))
      (by have := slot_le (w := wx) hj; omega)
  refine ⟨⟨hct, hmt, (htarr aR2 (by decide)).trans hvr, ?_,
    (htarr aY (by decide)).trans hv, Nat.mod_lt _ (by omega), ?_, ?_,
    source_tail (work_source h.ctx hf hk h.source)⟩, ?_, hf, hk⟩
  · intro i hi hne
    rw [hft.word (Or.inr (by have := hdr_lt_slot wx aX (show Crt.sRem < 32 by decide); omega)) (by omega)]
    exact hvhigh i hi hne
  · exact (hft.word (by unfold Crt.sSrc Crt.sRem sFn; omega) (by decide)).trans hvptr
  · simpa only [List.length_cons, Nat.add_sub_cancel] using htrem
  · simpa only [List.length_cons, Nat.add_eq_right] using htz

end VG.Proof.Dsa.X86_64
