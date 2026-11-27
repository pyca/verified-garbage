module

public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Dsa.AArch64.ReduceRead`, which this module and modules that import it used -/

section

/-! # Reading a byte for DSA streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Replacing the low word when every higher word is zero. -/
theorem write_low_value {mem : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w)
    (hbound : d + 8 * w ≤ 2 ^ 64) (value : BitVec 64)
    (hzero : ∀ i < w, i ≠ 0 → word mem B (d + 8 * i) = 0) :
    wv (mem.writeW (off B d) value) B d w = value.toNat := by
  have hout := writeW_outside mem B value (show d + 8 ≤ 2 ^ 64 by omega_using [hw, hbound])
  have h := wv_single (mem.writeW (off B d) value) B d (i := 0) w (by omega_using [hw])
    (fun i hi hne => by rw [hout.word (by omega_using [hne]) (by omega_using [hbound, hi])]; exact hzero i hi hne)
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
  refine WP.mono (WP.keep [.x1, .x3, .x8] (Q := fun t =>
    t.mem = (s.mem.writeW (off B (slot w aX)) ((s.mem p).zeroExtend 64)).writeW
      (off B (8 * Crt.sSrc)) (p + 1)) ?_ rfl rfl rfl)
    fun t ⟨hm, hk⟩ => ⟨hm, hk.mono (by decide)⟩
  unfold Arithmetic.reduceRead
  brun [hg.x0, hdr_enc (show Crt.sSrc < 32 by decide), hdr_enc (show sArr aX < 32 by decide),
    hp, hg.hdr.harr aX (by decide),
    hg.scr.ld (show 8 * Crt.sSrc + 8 ≤ Z by omega),
    hg.scr.ld (show 8 * sArr aX + 8 ≤ Z by omega), hr,
    hg.scr.st (show slot w aX + 8 ≤ Z by omega),
    hg.scr.st (show 8 * Crt.sSrc + 8 ≤ Z by omega)]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat,
    BitVec.zeroExtend]
  have := (s.mem p).isLt
  simp
  omega

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
    writeW_outside _ _ _ (by omega_using [hz, hslot])
  have ha : Arrays (off B o) wx [aX] s.mem first :=
    Arrays.of_outside (List.mem_singleton_self aX) ho (Nat.le_refl _) (by omega_using [])
  have hs : Outside (off B o) (8 * Crt.sSrc) 8 first t.mem := by
    rw [hmem]
    exact writeW_outside _ _ _ (by decide)
  have hfw : Frm (off B o) (workRanges wx) first t.mem := by
    intro x hx
    apply hs x
    have h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
    have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
    unfold Crt.sSrc sFn at *
    omega
  have hf := (arrays_work (js := [aX]) ha (by decide)).trans hfw
  have ht := hc.of_frmT hf (workRanges_ok wx) hk.wr (hk.gpr .x0 (by decide))
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
      write_low_value hw (by omega_using [hz, hslot]) _ hzero]
    change ((s.mem p).setWidth 64).toNat = (s.mem p).toNat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (s.mem p).isLt (show 2 ^ 8 < 2 ^ 64 by decide))]
  · intro i hi hne
    rw [hs.word (Or.inr (by have := hdr_lt_slot wx aX (show Crt.sSrc < 32 by decide); omega_using [this]))
      (by omega_using [hz, hslot, hi]), ho.word (by omega_using [hne]) (by omega_using [hz, hslot, hi])]
    exact hzero i hi hne
  · rw [hmem, word_writeW_self]
  · rw [hs.word (by unfold Crt.sSrc Crt.sRem sFn; omega_using []) (by decide)]
    exact ho.word (Or.inl (by have := hdr_lt_slot wx aX (show Crt.sRem < 32 by decide); omega_using [this])) (by decide)

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.Arithmetic`, which only this module used -/

section

/-! # Correctness of DSA's AArch64 byte-reduction arithmetic -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Horner reduction's arithmetic step, using any verified Montgomery
backend. The modulus can be composite. The byte is represented by array 1;
array 4 holds 256R mod m and is preserved. -/
theorem reduceStep_ok (M : Mont) {s : State} {B : Addr} {Z w m y byte : Nat}
    {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hn : wv s.mem B (slot w aN) w = m) (hm : m % 2 = 1)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hy : wv s.mem B (slot w aY) w = y) (hyl : y < m)
    (hb : wv s.mem B (slot w aX) w = byte) (hbyte : byte < m)
    (hc : wv s.mem B (slot w aXm) w = 256 * 2 ^ (64 * w) % m) :
    WP isa (VG.Impl.Dsa.AArch64.Arithmetic.reduceStep M.mm) s fun t =>
      Good t B Z w minv ∧
      wv t.mem B (slot w aY) w = (256 * y + byte) % m ∧
      Arrays B w [aAcc, aTmp, aY] s.mem t.mem ∧ Keep mmRegs s t := by
  have hnZ : B.toNat + slot w 8 ≤ 2 ^ 64 := by
    have := hg.scr.nowrap
    omega_using [hZ, this]
  unfold VG.Impl.Dsa.AArch64.Arithmetic.reduceStep
  refine WP.seq (WP.mono (M.mm_ok hg hZ hw hw' (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hinv ?_) fun u h => ?_)
  · rw [hy, hn]
    exact hyl
  obtain ⟨hu, hlu, hmu, hfu, hku⟩ := h
  have un : wv u.mem B (slot w aN) w = m :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hn
  have ub : wv u.mem B (slot w aX) w = byte :=
    (hfu.wv_of_not_mem (by decide) (by decide) hnZ).trans hb
  rw [hn, hy, hc, Nat.mul_comm (256 * 2 ^ (64 * w) % m) y] at hmu
  rw [hn] at hlu
  have uy := VG.Proof.Dsa.mont_scale (coprime_pow2 hm (64 * w)) hmu
  rw [Nat.mod_eq_of_lt hlu, Nat.mul_comm y 256] at uy
  refine WP.mono (addMod_ok hu.scr hu.x0 hu.hdr hZ hw hw'
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [un]; exact hlu) (by rw [ub, un]; exact hbyte)) fun t ht => ?_
  obtain ⟨hv, hf, hk⟩ := ht
  refine ⟨⟨hu.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hu.x0, hf.hdr hu.hdr⟩,
    ?_, hfu.trans hf, (hku.trans hk).mono (by decide)⟩
  rw [uy, ub, un] at hv
  rw [hv, Nat.mod_add_mod]

end VG.Proof.Dsa.AArch64

end

end

/-! # A complete byte step of DSA's streaming modular reduction -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Facts retained as the byte loop advances. -/
structure ReduceState (s : State) (B : Addr) (Z o w wx m : Nat) (minv : BitVec 64)
    (p : Addr) (bytes : List Byte) (acc : Nat) : Prop where
  ctx : SubCtx s B Z o w wx minv
  modulus : ModCtx s (off B o) (slot wx 8) wx minv m
  multiplier : wv s.mem (off B o) (slot wx aXm) wx = 256 * 2 ^ (64 * wx) % m
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
      t.gpr .x3 = BitVec.ofNat 64 bs.length ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hr : InRegions (s.rd ++ s.wr) p 1 := by simpa using h.source.rd 0 (by simp)
  have hb : s.mem p = b := by
    have hv := h.source.val 0 (by simp)
    change s.mem (p + 0) = b at hv
    exact (congrArg s.mem (BitVec.add_zero p)).symm.trans hv
  have hz := h.ctx.good.scr.nowrap
  have hslot := slot_le (w := wx) (show aX < 8 by decide)
  unfold Arithmetic.reduceByte seqs
  refine WP.seq (WP.mono (reduceRead_context h.ctx h.modulus (by omega_using [hw]) h.pointer hr h.high)
    fun u ⟨hcu, hmu, hbyte, hkept, hhigh, hptr, hrem, hfu, hku⟩ => ?_)
  rw [hb] at hbyte
  have huy := (hkept aY (by decide) (by decide)).trans h.value
  have hur := (hkept aXm (by decide) (by decide)).trans h.multiplier
  refine WP.seq (WP.mono (reduceStep_ok M hcu.good (Nat.le_refl _) hw hw'
    hmu.modulus hodd hmu.inverse huy h.reduced hbyte (by have := b.isLt; omega_using [hm]) hur)
    fun v ⟨hgv, hv, hfv, hkv⟩ => ?_)
  have hcv := arrays_context hcu hfv (by decide) hkv
  have hn := (hfv.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hmu.modulus
  have hi : ((word v.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfv.word0_of_not_mem (by decide) (by decide) hz (by omega_using [hw])]
    exact hmu.inverse
  have hmv : ModCtx v (off B o) (slot wx 8) wx minv m := ⟨hgv, hn, hi⟩
  have hvr := (hfv.wv_of_not_mem (show aXm < 8 by decide) (by decide) hz).trans hur
  have hvptr := (hfv.hslot (i := Crt.sSrc) (by decide)).trans hptr
  have hvrem := ((hfv.hslot (i := Crt.sRem) (by decide)).trans hrem).trans h.remaining
  have hvhigh : ∀ i < wx, i ≠ 0 → word v.mem (off B o) (slot wx aX + 8 * i) = 0 := by
    intro i hi hne
    rw [hfv.word_eq (fun j hj => by
      have hne : aX ≠ j := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> decide
      have := slot_sep (w := wx) hne
      omega_using [hi, this]) (by omega_using [hz, hslot, hi])]
    exact hhigh i hi hne
  have hfw := hfu.trans (arrays_work hfv (by decide))
  have hkw := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.mono (reduceCount_ok hcv hmv hvrem (by simp) hlen)
    fun t ⟨hct, hmt, htrem, htz, hft, hftw, hkt⟩ => ?_
  have hf := hfw.trans hftw
  have hk := (hkw.trans hkt).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have htarr : ∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv v.mem (off B o) (slot wx j) wx := by
    intro j hj
    exact hft.wv (Or.inr (by have := hdr_lt_slot wx j (show Crt.sRem < 32 by decide); omega_using [this]))
      (by have := slot_le (w := wx) hj; omega_using [hz, this])
  refine ⟨⟨hct, hmt, (htarr aXm (by decide)).trans hvr, ?_,
    (htarr aY (by decide)).trans hv, Nat.mod_lt _ (by omega_using [hm]), ?_, ?_,
    source_tail (work_source h.ctx hf hk h.source)⟩, ?_, hf, hk⟩
  · intro i hi hne
    rw [hft.word (Or.inr (by have := hdr_lt_slot wx aX (show Crt.sRem < 32 by decide); omega_using [this])) (by omega_using [hz, hslot, hi])]
    exact hvhigh i hi hne
  · exact (hft.word (by unfold Crt.sSrc Crt.sRem sFn; omega_using []) (by decide)).trans hvptr
  · simpa only [List.length_cons, Nat.add_sub_cancel] using htrem
  · simpa only [List.length_cons, Nat.add_sub_cancel] using htz

end VG.Proof.Dsa.AArch64
