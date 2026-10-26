module
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame

import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! # Reading a byte for DSA streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Replacing the low word when every higher word is zero. -/
theorem write_low_value {mem : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w)
    (hbound : d + 8 * w ≤ 2 ^ 64) (value : BitVec 64)
    (hzero : ∀ i < w, i ≠ 0 → word mem B (d + 8 * i) = 0) :
    wv (mem.writeW (off B d) value) B d w = value.toNat := by
  have hout := writeW_outside mem B value (show d + 8 ≤ 2 ^ 64 by omega)
  have h := wv_single (mem.writeW (off B d) value) B d (i := 0) w (by omega)
    (fun i hi hne => by rw [hout.word (by omega) (by omega)]; exact hzero i hi hne)
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.mul_one, word_writeW_self] using h

/-- The byte reader accesses exactly the current source byte and the
workspace's byte array and source-pointer slot. -/
theorem reduceRead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w)
    {p : Addr} (hp : word s.mem B (8 * Crt.sSrc) = p)
    (hr : InRegions (s.rd ++ s.wr) p 1) :
    WP isa (.block Arithmetic.reduceRead) s fun t =>
      t.mem = (s.mem.writeW (off B (slot w aX)) ((s.mem p).zeroExtend 64)).writeW
        (off B (8 * Crt.sSrc)) (p + 1) ∧ Keep mmRegs s t := by
  have hslot := slot_le (w := w) (show aX < 8 by decide)
  have hptr := hdr_lt_slot w 8 (show Crt.sSrc < 32 by decide)
  have harr := hdr_lt_slot w 8 (show sArr aX < 32 by decide)
  refine WP.mono (WP.keep [.rsi, .rax, .rbx] (Q := fun t =>
    t.mem = (s.mem.writeW (off B (slot w aX)) ((s.mem p).zeroExtend 64)).writeW
      (off B (8 * Crt.sSrc)) (p + 1)) ?_ rfl)
    fun t ⟨hm, hk⟩ => ⟨hm, hk.mono (by decide)⟩
  have h0 : ∀ x : Addr, x + BitVec.ofInt 64 0 = x := fun x => BitVec.add_zero x
  unfold Arithmetic.reduceRead
  xrun [State.ea, hdr, at0, h0, BitVec.add_zero, hg.rdi, hdrOff, hp, hg.hdr.harr aX (by decide),
    hg.scr.ld (show 8 * Crt.sSrc + 8 ≤ Z by omega),
    hg.scr.ld (show 8 * sArr aX + 8 ≤ Z by omega), hr,
    hg.scr.st (show slot w aX + 8 ≤ Z by omega),
    hg.scr.st (show 8 * Crt.sSrc + 8 ≤ Z by omega)]

/-- The reader preserves the accumulator, multiplier, modulus, source count,
and zero high words of the byte array. -/
theorem reduceRead_context {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 1 ≤ wx) {p : Addr} (hp : word s.mem (off B o) (8 * Crt.sSrc) = p)
    (hr : InRegions (s.rd ++ s.wr) p 1)
    (hzero : ∀ i < wx, i ≠ 0 → word s.mem (off B o) (slot wx aX + 8 * i) = 0) :
    WP isa (.block Arithmetic.reduceRead) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aX) wx = (s.mem p).toNat ∧
      (∀ j < 8, j ≠ aX → wv t.mem (off B o) (slot wx j) wx =
        wv s.mem (off B o) (slot wx j) wx) ∧
      (∀ i < wx, i ≠ 0 → word t.mem (off B o) (slot wx aX + 8 * i) = 0) ∧
      word t.mem (off B o) (8 * Crt.sSrc) = p + 1 ∧
      word t.mem (off B o) (8 * Crt.sRem) = word s.mem (off B o) (8 * Crt.sRem) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := hc.good.scr.nowrap
  have hslot := slot_le (w := wx) (show aX < 8 by decide)
  refine WP.mono (reduceRead_ok hc.good (Nat.le_refl _) hw hp hr) fun t ⟨hmem, hk⟩ => ?_
  let first := s.mem.writeW (off (off B o) (slot wx aX)) ((s.mem p).zeroExtend 64)
  have ho : Outside (off B o) (slot wx aX) 8 s.mem first :=
    writeW_outside _ _ _ (by omega)
  have ha : Arrays (off B o) wx [aX] s.mem first :=
    Arrays.of_outside (List.mem_singleton_self aX) ho (Nat.le_refl _) (by omega)
  have hs : Outside (off B o) (8 * Crt.sSrc) 8 first t.mem := by
    rw [hmem]
    exact writeW_outside _ _ _ (by decide)
  have hfw : Frm (off B o) (workRanges wx) first t.mem := by
    intro x hx
    apply hs x
    have h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
    have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
    unfold Crt.sSrc sFn at *
    omega
  have hf := (arrays_work (js := [aX]) ha (by decide)).trans hfw
  have ht := hc.of_frmT hf (workRanges_ok wx) hk.2.2 (hk.gpr (by decide))
  have heq : ∀ j < 8, j ≠ aX → wv t.mem (off B o) (slot wx j) wx =
      wv s.mem (off B o) (slot wx j) wx := by
    intro j hj hjx
    rw [hmem, hdrStore_wv _ _ _ (by decide) hj hz]
    exact ha.wv_of_not_mem hj (by simpa using hjx) hz
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem, hdrStore_word _ _ _ (by decide) (by decide) hz,
      ha.word0_of_not_mem (by decide) (by decide) hz hw]
    exact hm.inverse
  refine ⟨ht, ⟨ht.good, (heq aN (by decide) (by decide)).trans hm.modulus, hi⟩,
    ?_, heq, ?_, ?_, ?_, hf, hk⟩
  · rw [hmem, hdrStore_wv _ _ _ (by decide) (by decide) hz,
      write_low_value hw (by omega) _ hzero]
    change ((s.mem p).setWidth 64).toNat = (s.mem p).toNat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (s.mem p).isLt (show 2 ^ 8 < 2 ^ 64 by decide))]
  · intro i hi hne
    rw [hs.word (Or.inr (by have := hdr_lt_slot wx aX (show Crt.sSrc < 32 by decide); omega))
      (by omega), ho.word (by omega) (by omega)]
    exact hzero i hi hne
  · rw [hmem, word_writeW_self]
  · rw [hs.word (by unfold Crt.sSrc Crt.sRem sFn; omega) (by decide)]
    exact ho.word (Or.inl (by have := hdr_lt_slot wx aX (show Crt.sRem < 32 by decide); omega)) (by decide)

end VG.Proof.Dsa.X86_64
